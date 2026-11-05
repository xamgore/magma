# Local `.lake` workspace

`.lake` is ignored by Git. Keep the root tidy: only Lake-owned caches,
explicitly retained research context and named data directories belong here.
Do not put temporary proofs, log files, scripts or diagnostics directly in it.

## Do not delete

- `ROADMAP.md`, `plan.md`: user-maintained research plans; neither is generated.
- `portable-rc2/`: user-maintained offline Linux/Lean RC2 packaging work,
  including `build.py` and `finalize.py`. This folder is **not** a scratch cache.
- `build/`: Lake-generated `.olean`, native executables and build metadata.
- `packages/`: checked-out dependencies, their own build caches and Git history.
- `config/`: Lake configuration cache and generated traces.

Deleting `build/` or `packages/` would cause expensive rebuilds/downloads.
Use Lake's own commands when deliberately rebuilding dependencies.

## Data directories

- `exports/`: regenerated `.lake/exports/defs.txt` (definitions) and
  `.lake/exports/sources.txt` (original source bundle). `lake exe defs` writes
  both; `python3 scripts/export_sources.py -o .lake/exports/sources.txt`
  writes only the source bundle. `exports/handoff/` holds explicit handoffs.
- `work/`: **disposable** task-specific files. Agents write to `work/agent/`;
  `scripts/accept_lean.py` writes diagnostics to `work/accept_lean/` and removes
  its successful finishing log. Other scripts should use their own `work/<name>/`
  directory, not the `.lake` root.
- `state/`: intake fingerprints and duplicate-failure suppression for
  `scripts/accept_lean.py`; deleting it changes the workflow behavior.
- `archive/`: historical material not needed by current builds. The previous
  formatter forks and source snapshots live under `archive/tooling/`, old
  one-off checkout/refactoring scripts under `archive/scripts/`, and layout
  metadata under `archive/metadata/`. This archive is not imported, and no
  script should write new files there automatically.

The relevant **Magma research experiments** recovered from `.lake` now live
beside their subjects: `Magma/DDT/Experiments/Probes/`,
`Magma/Differential/{LocalDDT,EightRounds,FourRounds,Windows}/Experiments/Probes/`,
`Magma/Differential/FiveRounds/Experiments/Probes/`, and
`Magma/Search/Experiments/Legacy/`. Historical or outdated sketches are not
part of ordinary builds. The modern numbered DDT iterations remain under
`Magma/DDT/Experiments/`.

## Cleaning

```sh
python3 scripts/clean_lake.py             # dry run; changes nothing
python3 scripts/clean_lake.py --apply     # remove only .lake/work/
```

Run cleanup after task processes have exited, never while a detached job is
writing files. Explicit optional flags `--exports`, `--state` and `--archive`
allow deleting those categories too; **these are not used in routine cleanup**.
`--archive` can delete unique historical material and is deliberately opt-in.
None of these commands touches the three protected research items or the
Lake-owned build, package or config caches.

The original GitHub Actions workflow builds the checked-out commit, not the
local Mac working tree. A job ending with exit code 143 received `SIGTERM`;
that result alone does not distinguish cancellation, a runner timeout, or
other external termination. Check the GitHub job's summary and event timeline
before diagnosing it as a Lean proof failure.
