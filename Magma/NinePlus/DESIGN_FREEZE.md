# Design freeze — active 9+ exploration only

Status: 2026-11-03.

## FROZEN until a concrete downstream gain

- The 1024 certified nine-round one-hot positives. They are still
  checkable through `lake build Magma.Diffan.Certificates`. Do not
  move/rename them or generate another bulk certificate matrix.
- Eight-round 1125 rectangle UNSAT formal certificates. Current Z3
  evidence and conditional Lean soundness are retained. Unfreeze only
  if forbidden eight-round edges remove surviving paths in a
  measured 10+ round search.
- Five-round full 2-hot -> 2-hot SAT matrix. The computational
  evidence and reusable structural theorems remain; no manual
  pair-by-pair Lean proof without a new generalizable technique.
- Generic refactors of unrelated `Magma/Diffan` sources and
  retroactive rewrite of Git history.

- Repeating the 8x8 sparse outer comparison at longer Z3 timeouts:
  design-frozen after **64 SAT in both models** at a 600000-ms
  per-cell limit; see `results/linked_600s_all64.json`.
- Generating additional one-hot or two-hot positive certificates
  for the already SAT-covered nine-round outer family.

## ACTIVE, with explicit stop conditions

- Does RFC linked-key support give strict pruning beyond independent
  real g-support? Stop if controlled experiments find only SAT/UNKNOWN
  and no testable stronger invariants.
- Does the 8-round palindrome + appended round yield constraints
  beyond known reflection attacks? A bare involution is NOT an ID.
- Can actual correlated carry/base constraints cheaply reject a
  nine-round class and scale to a 10+ round obstruction?

## Working rules

`sorry`, `axiom`, and `variable` are permitted for experimental
hypotheses, provided the relevant file and theorem are labeled
SPECULATIVE, and nothing is described as unconditional/kernel-proved.
Prefer conditional theorems parameterized by explicit hypotheses.

Do not import speculative modules or mass evidence into the main
`Magma.lean`. Keep exact solver arguments, status taxonomy,
replay checks, and a concise README inside each active research folder.
Use long timeouts only for selected promising unresolved cells.
