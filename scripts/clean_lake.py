#!/usr/bin/env python3
"""Clean only explicitly designated disposable files inside .lake.

Without --apply, print the paths that would be removed. By default only
.lake/work is selected. Other categories require explicit flags.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import shutil

LAKE = Path(__file__).resolve().parents[1] / '.lake'
OPTIONAL = {'exports': 'exports', 'archive': 'archive', 'state': 'state'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true', help='Actually delete selected directories')
    parser.add_argument('--exports', action='store_true', help='Also delete regenerable exports and handoffs')
    parser.add_argument('--archive', action='store_true', help='Also delete historical sources (potentially unique!)')
    parser.add_argument('--state', action='store_true', help='Also delete intake fingerprints and wakeup state')
    args = parser.parse_args()
    targets = ['work'] + [name for flag, name in OPTIONAL.items() if getattr(args, flag)]
    for name in targets:
        target = LAKE / name
        if not target.exists() and not target.is_symlink():
            print(f'Absent: {target}')
            continue
        if not LAKE.is_dir() or LAKE.is_symlink() or target.is_symlink() or not target.is_dir():
            raise SystemExit(f'Refusing to delete unexpected directory/symlink: {target}')
        if args.apply:
            shutil.rmtree(target)
            print(f'Deleted: {target}')
        else:
            print(f'Would delete: {target} (pass --apply to confirm)')
    if not args.apply:
        print('No files deleted.')


if __name__ == '__main__':
    main()
