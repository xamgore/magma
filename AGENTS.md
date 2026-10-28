Don't write reports anywhere except the chat unless requested.
When updating README.md, only extend the existing blocks.

All project Lean sources must use the module system and include `import all Init.Data.Range.Basic` unconditionally. Include this import when adapting incoming Lean files, even if they contain no range loops. Full imports are not re-exported transitively.

Keep project-wide Lean options in `leanOptions` in `lakefile.toml`, rather than duplicating `set_option` in source files. Use `lake lean <file>` for manual elaboration with these options.

First elaborate changed Lean modules and fix proof errors before running the formatter. Then run mechanical formatting, final validation, axiom audit, and commit steps as one detached job. Redirect all output to `.lake/out.txt` and use `osascript` to notify completion or failure. Do not poll these jobs; inspect failures only when debugging. Stage and commit only task-owned paths.

Use `python3 scripts/accept_lean.py prepare/check/finish` for incoming modules. Review actual `example`/`#eval` commands for Evidence before choosing the destination. Do not run `git status` during routine intake or detached finishing. For heartbeat/recursion failures, request targeted Lean diagnostics before changing resource limits.
