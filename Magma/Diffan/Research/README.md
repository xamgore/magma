# Magma / Diffan research packages

This directory contains **scientific work in progress**, grouped by
question rather than by proof script. A research package can include
a short README, optional Lean `Prop` models, a solver/Rust experiment,
fixtures and a small machine-readable report. Compiled libraries in
`Magma/Diffan/*.lean` remain in their existing locations to avoid
breaking imports and expensive Lean rebuilds.

## NinePlus — active

`NinePlus/README.md`: investigate key-independent impossible
differentials at 9+ ordinary rounds, with emphasis on the RFC
palindromic key-schedule boundary. Includes:
- `Model.lean` — independently chosen versus shared subkey
  necessary conditions, plus an explicit *conditional* soundness rule
- `ParityCollision.lean` — genuine kernel-checked key parity collision
- `local_key_coupling.py` — bounded Z3 comparison, keeps UNKNOWN distinct
- `reflection_window20.py`, `fixtures/`, `results/` — reproducibility
- `DESIGN_FREEZE.md` — defer nonessential bulk formalization

## Frozen or archived work

- General reusable Feistel/word-chain/carry theory:
  `Magma/Diffan/OuterWordRecurrence.lean`,
  `IndependentRoundSupport.lean` and core reduction lemmas. These
  are root-imported mathematical results, not active research scripts.
- Large nine-round one-hot positive witness certificates remain in
  `Magma/Diffan/NineRoundPositiveRows/`, opt-in via
  `lake build Magma.Diffan.Certificates`.
- Eight-round rectangle Z3 experiments, hypotheses and longer
  chronology are documented in `research/SPARSE_WINDOWS.md`
  and `research/archive/SPARSE_WINDOWS_HISTORY.md`.

**Triage rule:** an observation should first demonstrate stronger
pruning or a new parameterized property before generating many
Lean proofs. Research-specific `sorry`, `axiom` or `variable`
are permitted only when labeled speculative and cannot be presented
as kernel-established facts.
