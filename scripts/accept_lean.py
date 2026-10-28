#!/usr/bin/env python3
"""Prepare an incoming Lean module, check proofs, then finish in the background."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / '.lake/out.txt'
RANGE_IMPORT = 'import all Init.Data.Range.Basic'


def code_only(source: str) -> str:
    """Mask comments and strings, preserving line positions for command detection."""
    out = list(source)
    i = depth = 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                width = 2
            elif source.startswith('-/', i):
                depth -= 1
                width = 2
            else:
                width = 1
        elif source.startswith('/-', i):
            depth = 1
            width = 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            width = (len(source) if end < 0 else end) - i
        elif source[i] == '"':
            end = i + 1
            while end < len(source):
                if source[end] == '\\':
                    end += 2
                elif source[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            width = end - i
        else:
            i += 1
            continue
        for j in range(i, min(i + width, len(source))):
            if source[j] != '\n':
                out[j] = ' '
        i += width
    return ''.join(out)


def relative_file(value: str) -> Path:
    path = (ROOT / value).resolve()
    path.relative_to(ROOT)
    if path.suffix != '.lean':
        raise ValueError('Expected a project .lean file')
    return path


def module_name(path: Path) -> str:
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)


def prepare(args: argparse.Namespace) -> None:
    dest = relative_file(args.file)
    if dest.exists():
        raise ValueError(f'Refusing to overwrite {dest}')
    source = Path(args.source).expanduser().read_text()
    masked = code_only(source)
    findings = [(masked.count('\n', 0, m.start()) + 1, m.group(1))
                for m in re.finditer(r'^[ \t]*(example\b|#eval\b)', masked, re.M)]
    print('Evidence review: ' + (', '.join(f'{kind} at {line}' for line, kind in findings)
                                if findings else 'no example/#eval commands'))
    if findings and 'Evidence' not in dest.relative_to(ROOT).parts and not args.keep_examples:
        raise ValueError('Review example/#eval commands for Evidence first; '
                         'use --keep-examples only for intentional library certificates')
    # Incoming per-proof resource overrides are replaced by proof adaptation,
    # rather than silently changing project-wide limits.
    source, removed = re.subn(
        r'^set_option (?:maxRecDepth|maxHeartbeats) \d+ in\s*\n', '', source, flags=re.M)
    module_header = re.search(r'^[ \t]*module[ \t]*\n', code_only(source), re.M)
    if module_header:
        source = source[:module_header.start()] + source[module_header.end():]
    imports = [f'public import {name}' for name in args.imports]
    imports.append(RANGE_IMPORT)
    body_lines = source.splitlines()
    existing = []
    masked_lines = code_only(source).splitlines()
    for index, line in enumerate(masked_lines):
        if re.fullmatch(r'\s*(?:(?:public|meta)\s+)*import\s+.*', line):
            existing.append(body_lines[index].strip())
            body_lines[index] = ''
    imports = list(dict.fromkeys(imports + existing))
    section = '' if re.search(r'\bpublic section\b', code_only(source)) else '@[expose] public section\n\n'
    result = 'module\n\n' + '\n'.join(imports) + '\n\n' + section
    result += '\n'.join(body_lines).lstrip() + '\n'
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(result)
    if 'Evidence' not in dest.relative_to(ROOT).parts:
        root_file = ROOT / 'Magma.lean'
        root_source = root_file.read_text()
        entry = f'public import {module_name(dest)}\n'
        if entry not in root_source:
            root_source = root_source.replace(RANGE_IMPORT, entry + RANGE_IMPORT, 1)
            root_file.write_text(root_source)
    print(f'Prepared {dest.relative_to(ROOT)}; removed {removed} local resource overrides')


def proof_stamp(path: Path) -> Path:
    return ROOT / '.lake/intake' / (module_name(path) + '.sha256')


def fingerprint(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(args: argparse.Namespace) -> None:
    path = relative_file(args.file)
    LOG.parent.mkdir(exist_ok=True)
    stamp = proof_stamp(path)
    stamp.unlink(missing_ok=True)
    checked_hash = fingerprint(path)
    with LOG.open('w') as log:
        result = subprocess.run(['lake', 'build', str(path.relative_to(ROOT))],
                                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        errors = re.findall(r'^error:.*', LOG.read_text(), re.M)
        print('\n'.join(errors[:12]))
        print(f'{len(errors)} errors; full diagnostics: {LOG}')
    elif fingerprint(path) == checked_hash:
        stamp.parent.mkdir(parents=True, exist_ok=True)
        stamp.write_text(checked_hash)
    else:
        raise ValueError('Source changed during proof checking; check it again')
    raise SystemExit(result.returncode)


def finish(args: argparse.Namespace) -> None:
    path = relative_file(args.file)
    paths = list(dict.fromkeys([str(path.relative_to(ROOT))] + args.paths))
    for owned in paths:
        (ROOT / owned).resolve().relative_to(ROOT)
    lean_files = [owned for owned in paths if owned.endswith('.lean') and owned != 'Magma.lean']
    commands = [
        ['lake', 'exe', 'fmt', 'format', '--workers', '1', *lean_files],
        ['lake', 'build', *lean_files, 'Magma'],
        ['lake', 'exe', 'axiom-audit', '--root', module_name(path)],
        ['git', 'diff', '--check', '--', *paths],
        ['git', 'add', '--', *paths],
        ['git', 'commit', '--only', '-m', args.message, '--', *paths],
    ]
    code = 0
    try:
        for command in commands:
            print('+', repr(command), flush=True)
            subprocess.run(command, cwd=ROOT, check=True)
    except subprocess.CalledProcessError as exc:
        code = exc.returncode
    except Exception as exc:
        print(str(exc), flush=True)
        code = 1
    finally:
        print(f'Completed with exit code {code}', flush=True)
        message = f'{path.stem}: ' + ('checks passed, commit created.' if code == 0 else 'check failed.')
        subprocess.run(['/usr/bin/osascript', '-', message], input='''on run argv
  display notification (item 1 of argv) with title "Magma"
end run
''', text=True, check=False)
    raise SystemExit(code)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    prep = sub.add_parser('prepare', help='Inspect Evidence commands, add headers and register the module')
    prep.add_argument('source')
    prep.add_argument('file')
    prep.add_argument('--import', dest='imports', action='append', default=[])
    prep.add_argument('--keep-examples', action='store_true')
    check_parser = sub.add_parser('check', help='Elaborate proofs before formatting; log failures')
    check_parser.add_argument('file')
    for action in ['finish', '_finish']:
        final = sub.add_parser(action, help='Detach formatting, validation, audit and commit')
        final.add_argument('file')
        final.add_argument('--path', dest='paths', action='append', default=[])
        final.add_argument('--message', required=True)
    args = parser.parse_args()
    if args.action == 'prepare':
        prepare(args)
    elif args.action == 'check':
        check(args)
    elif args.action == '_finish':
        finish(args)
    else:
        path = relative_file(args.file)
        lean_files = [path] + [relative_file(owned) for owned in args.paths
                               if owned.endswith('.lean') and owned != 'Magma.lean']
        for checked in lean_files:
            stamp = proof_stamp(checked)
            if not stamp.exists() or stamp.read_text() != fingerprint(checked):
                raise ValueError(f'Run check successfully before finish: {checked}')
        LOG.parent.mkdir(exist_ok=True)
        with LOG.open('a') as log:
            subprocess.Popen([sys.executable, str(Path(__file__).resolve()), '_finish', *sys.argv[2:]],
                             cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log,
                             stderr=subprocess.STDOUT, start_new_session=True)
        print(f'Detached; log: {LOG}')


if __name__ == '__main__':
    main()
