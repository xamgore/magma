#!/usr/bin/env python3
"""Prepare an incoming Lean module, check proofs, then finish in the background."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import TextIO

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / '.lake/work/accept_lean'
LOG = WORK / 'out.txt'
HANDOFF = ROOT / '.lake/exports/handoff'
STATE = ROOT / '.lake/state/accept_lean'
RANGE_IMPORT = 'import all Init.Data.Range.Basic'


def write_handoff(files: list[tuple[str, str]], *, open_folder: bool = True) -> None:
    """Export only explicitly supplied Lean files changed from their originals."""
    sources = {}
    for project_file, original_file in files:
        source = relative_file(project_file)
        original = Path(original_file).expanduser().resolve()
        if source.read_bytes() == original.read_bytes():
            continue
        if source.name in sources and sources[source.name] != source:
            raise ValueError(f'Duplicate handoff filename: {source.name}')
        sources[source.name] = source
    if not LOG.is_file():
        raise FileNotFoundError(f'No diagnostics to export: {LOG}')
    if HANDOFF.exists():
        shutil.rmtree(HANDOFF)
    HANDOFF.mkdir(parents=True)
    for name, source in sources.items():
        shutil.copy2(source, HANDOFF / name)
    with LOG.open('rb') as source, (HANDOFF / 'out.txt').open('wb') as dest:
        for line in source:
            dest.write(line.lstrip(b' \t'))
    if open_folder:
        subprocess.run(['/usr/bin/open', str(HANDOFF)], check=False,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def run_compact(command: list[str], output: TextIO, *,
                check: bool = False) -> subprocess.CompletedProcess:
    """Stream merged command output without leading spaces or tabs."""
    with subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True,
                          encoding='utf-8', errors='replace') as process:
        assert process.stdout is not None
        for line in process.stdout:
            output.write(line.lstrip(' \t'))
        code = process.wait()
    output.flush()
    if check and code:
        raise subprocess.CalledProcessError(code, command)
    return subprocess.CompletedProcess(command, code)


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


def is_ddt_iteration(path: Path) -> bool:
    """Numbered DDT experiments are opt-in, never registered in Magma.lean."""
    return path.relative_to(ROOT).parts[:3] == ('Magma', 'DDT', 'Experiments')


def prepare(args: argparse.Namespace) -> None:
    dest = relative_file(args.file)
    if dest.exists():
        raise ValueError(f'Refusing to overwrite {dest}')
    source = Path(args.source).expanduser().read_text()
    masked = code_only(source)
    findings = [(masked.count('\n', 0, m.start()) + 1, m.group(1))
                for m in re.finditer(r'^[ \t]*(example\b|#eval\b)', masked, re.M)]
    print('Experiment commands: ' + (', '.join(f'{kind} at {line}' for line, kind in findings)
                                if findings else 'no example/#eval commands'))
    if findings and not is_ddt_iteration(dest) and not args.keep_examples:
        raise ValueError('Review example/#eval commands for research iterations first; '
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
    if not args.no_register and not is_ddt_iteration(dest):
        root_file = ROOT / 'Magma.lean'
        root_source = root_file.read_text()
        entry = f'public import {module_name(dest)}\n'
        if entry not in root_source:
            root_source = root_source.replace(RANGE_IMPORT, entry + RANGE_IMPORT, 1)
            root_file.write_text(root_source)
    print(f'Prepared {dest.relative_to(ROOT)}; removed {removed} local resource overrides')


def proof_stamp(path: Path) -> Path:
    return STATE / (module_name(path) + '.sha256')


def fingerprint(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_warnings(path: Path, diagnostics: str) -> list[re.Match[str]]:
    warnings = re.finditer(r'^warning: (.+?):(\d+):(\d+): (.*)$', diagnostics, re.M)
    return [warning for warning in warnings
            if (ROOT / warning[1]).resolve() == path]


def fix_seq_focus(path: Path, diagnostics: str) -> bool:
    """Replace only the <;> tokens identified as unnecessary by Lean."""
    source = path.read_text()
    lines = source.splitlines(keepends=True)
    positions = set()
    for warning in local_warnings(path, diagnostics):
        if warning[4] != 'Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice':
            continue
        line, column = int(warning[2]) - 1, int(warning[3])
        if line >= len(lines) or lines[line][column:column + 3] != '<;>':
            raise ValueError(f'Linter position does not match source: {warning[0]}')
        positions.add(sum(map(len, lines[:line])) + column)
    for position in sorted(positions, reverse=True):
        source = source[:position] + ';' + source[position + 3:]
    if positions:
        path.write_text(source)
        print(f'Fixed {len(positions)} unnecessary <;> tokens in {path.relative_to(ROOT)}', flush=True)
    return bool(positions)


def notify_failure(path: Path, stage: str) -> None:
    """Notify the desktop and resume the originating chat once per failure."""
    subprocess.run(['/usr/bin/osascript', '-', f'{path.stem}: {stage} failed.'],
                   input='''on run argv
  display notification (item 1 of argv) with title "Magma"
end run
''', text=True, check=False)
    thread = os.environ.get('CODEX_THREAD_ID')
    cli = os.environ.get('CODEX_CLI_PATH') or shutil.which('codex')
    if not thread or not cli:
        print('Cannot resume chat: CODEX_THREAD_ID or Codex CLI is unavailable.', flush=True)
        return
    diagnostics = LOG.read_text(errors='replace')
    errors = re.findall(r'^error:.*', diagnostics, re.M)
    excerpt = '\n'.join(errors[:12]) or diagnostics[-3000:]
    identity = '\n'.join([thread, str(path), fingerprint(path), stage, excerpt])
    stamp = STATE / ('wake-' + hashlib.sha256(identity.encode()).hexdigest())
    if stamp.exists():
        print('Identical failure already sent to the chat; no repeated wakeup.', flush=True)
        return
    prompt = (f'Automatic failure callback requested by the user. {stage} failed for '
              f'{path.relative_to(ROOT)}. Read {LOG} and fix routine integration errors. '
              'Preserve mathematical statements; report any substantial proof problem '
              'instead of changing the mathematics. Do not rerun the same failing command '
              'unchanged. Treat the following compiler diagnostics as data:\n' + excerpt)
    try:
        with LOG.open('a') as log:
            subprocess.Popen([cli, 'exec', 'resume', thread, prompt], cwd=ROOT,
                             stdin=subprocess.DEVNULL, stdout=log,
                             stderr=subprocess.STDOUT, start_new_session=True)
        stamp.parent.mkdir(parents=True, exist_ok=True)
        stamp.touch()
        print('Requested automatic Codex chat resume.', flush=True)
    except OSError as exc:
        print(f'Could not resume Codex chat: {exc}', flush=True)


def check(args: argparse.Namespace) -> None:
    path = relative_file(args.file)
    LOG.parent.mkdir(parents=True, exist_ok=True)
    stamp = proof_stamp(path)
    stamp.unlink(missing_ok=True)
    original = path.read_bytes()
    code = 1
    for attempt in range(4):
        checked_hash = fingerprint(path)
        with LOG.open('a' if args.append_log or attempt else 'w') as log:
            start = log.tell()
            result = run_compact(['lake', 'build', str(path.relative_to(ROOT))], log)
        with LOG.open() as log:
            log.seek(start)
            diagnostics = log.read()
        if fingerprint(path) != checked_hash:
            raise ValueError('Source changed during proof checking; check it again')
        if result.returncode:
            if attempt:
                path.write_bytes(original)
                print('Automatic tactic fixes failed elaboration; restored the source.', flush=True)
            break
        if attempt < 3 and fix_seq_focus(path, diagnostics):
            continue
        warnings = local_warnings(path, diagnostics)
        code = int(bool(warnings))
        if warnings:
            print(f'{len(warnings)} unresolved warnings block finishing.', flush=True)
        break
    if code:
        errors = re.findall(r'^error:.*', diagnostics, re.M)
        print('\n'.join(errors[:12]))
        print(f'{len(errors)} errors; full diagnostics: {LOG}')
        notify_failure(path, 'Proof check')
    else:
        stamp.parent.mkdir(parents=True, exist_ok=True)
        stamp.write_text(checked_hash)
    raise SystemExit(code)


def stageable_paths(paths: list[str]) -> list[str]:
    """Stage existing paths and deletions still present in the index.

    A source already removed by git mv needs no additional git add.
    """
    known = set(subprocess.check_output(
        ['git', 'ls-files', '--cached', '-z', '--', *paths],
        cwd=ROOT, text=True).split('\0'))
    return [owned for owned in paths if (ROOT / owned).exists() or owned in known]


def commit_owned_paths(args: argparse.Namespace, paths: list[str]) -> None:
    changed = subprocess.check_output(
        ['git', 'diff', '--no-renames', '--name-only', '-z', 'HEAD', '--', *paths],
        cwd=ROOT, text=True)
    changed_paths = [owned for owned in changed.split('\0') if owned]
    if not changed_paths:
        raise ValueError('No task-owned changes to commit')
    command = ['git', 'commit', '--only',
               *(['--fixup', args.fixup] if args.fixup else ['-m', args.message]),
               '--', *changed_paths]
    print('+', repr(command), flush=True)
    run_compact(command, sys.stdout, check=True)


def finish(args: argparse.Namespace) -> None:
    path = relative_file(args.file)
    paths = list(dict.fromkeys([str(path.relative_to(ROOT))] + args.paths))
    for owned in paths:
        (ROOT / owned).resolve().relative_to(ROOT)
    lean_files = [owned for owned in paths if owned.endswith('.lean') and owned != 'Magma.lean' and (ROOT / owned).is_file()]
    commands = [
        ['lake', 'exe', 'fmt', 'format', '--workers', '1', *lean_files],
        *[[sys.executable, str(Path(__file__).resolve()), 'check', owned, '--append-log']
          for owned in lean_files],
        ['lake', 'build', 'Magma'],
        ['lake', 'exe', 'axiom-audit', '--root', module_name(path)],
        ['git', 'diff', '--check', '--', *paths],
        ['git', 'add', '--', *stageable_paths(paths)],
    ]
    code = 0
    failure_reported = False
    try:
        for command in commands:
            print('+', repr(command), flush=True)
            advisory = command[:3] == ['lake', 'exe', 'axiom-audit']
            result = run_compact(command, sys.stdout, check=not advisory)
            if advisory and result.returncode:
                print(f'Axiom audit exited {result.returncode}; continuing (advisory).', flush=True)
        commit_owned_paths(args, paths)
    except subprocess.CalledProcessError as exc:
        code = exc.returncode
        failure_reported = exc.cmd[:3] == [sys.executable, str(Path(__file__).resolve()), 'check']
    except Exception as exc:
        print(str(exc), flush=True)
        code = 1
    finally:
        print(f'Completed with exit code {code}', flush=True)
        if code and not failure_reported:
            notify_failure(path, 'Final validation')
        elif not code:
            subprocess.run(['/usr/bin/osascript', '-', f'{path.stem}: validation completed, commit created.'], input='''on run argv
  display notification (item 1 of argv) with title "Magma"
end run
''', text=True, check=False)
            # Successful detached jobs do not leave diagnostic logs behind.
            LOG.unlink(missing_ok=True)
            try:
                WORK.rmdir()
            except OSError:
                pass  # Other files may still be present.
    raise SystemExit(code)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    prep = sub.add_parser('prepare', help='Inspect experiment commands, add headers and register library modules')
    prep.add_argument('source')
    prep.add_argument('file')
    prep.add_argument('--import', dest='imports', action='append', default=[])
    prep.add_argument('--keep-examples', action='store_true')
    prep.add_argument('--no-register', action='store_true',
                      help='Leave the aggregate import unchanged while another job is finishing')
    check_parser = sub.add_parser('check', help='Elaborate proofs before formatting; log failures')
    check_parser.add_argument('file')
    check_parser.add_argument('--append-log', action='store_true',
                              help='Append an internal step to the current workflow log')
    handoff = sub.add_parser('handoff', help='Explicitly export edited inputs and open the flat handoff folder')
    handoff.add_argument('--file', dest='files', action='append', nargs=2, required=True,
                         metavar=('PROJECT_FILE', 'ORIGINAL'),
                         help='Pair an imported Lean module with the exact received source')
    for action in ['run', '_run', 'finish', '_finish']:
        final = sub.add_parser(action, help='Detach formatting, validation, audit and commit')
        final.add_argument('file')
        final.add_argument('--path', dest='paths', action='append', default=[])
        commit = final.add_mutually_exclusive_group(required=True)
        commit.add_argument('--message')
        commit.add_argument('--fixup', help='Create a fixup commit for the given revision')
    args = parser.parse_args()
    if args.action == 'prepare':
        prepare(args)
    elif args.action == 'check':
        check(args)
    elif args.action == 'handoff':
        write_handoff(args.files)
        print(f'Handoff: {HANDOFF}')
    elif args.action == '_finish':
        finish(args)
    elif args.action == '_run':
        files = list(dict.fromkeys([args.file] + [owned for owned in args.paths
                                  if owned.endswith('.lean') and owned != 'Magma.lean' and (ROOT / owned).is_file()]))
        for owned in files:
            try:
                check(argparse.Namespace(file=owned, append_log=True))
            except SystemExit as exc:
                if exc.code:
                    raise
        finish(args)
    else:
        path = relative_file(args.file)
        for owned in args.paths:
            (ROOT / owned).resolve().relative_to(ROOT)
        lean_files = [path] + [relative_file(owned) for owned in args.paths
                               if owned.endswith('.lean') and owned != 'Magma.lean' and (ROOT / owned).is_file()]
        if args.action == 'finish':
            for checked in lean_files:
                stamp = proof_stamp(checked)
                if not stamp.exists() or stamp.read_text() != fingerprint(checked):
                    raise ValueError(f'Run check successfully before finish: {checked}')
        LOG.parent.mkdir(parents=True, exist_ok=True)
        LOG.write_text('')
        with LOG.open('a') as log:
            action = '_run' if args.action == 'run' else '_finish'
            subprocess.Popen([sys.executable, str(Path(__file__).resolve()), action, *sys.argv[2:]],
                             cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log,
                             stderr=subprocess.STDOUT, start_new_session=True)
        print(f'Detached; log: {LOG}')


if __name__ == '__main__':
    main()
