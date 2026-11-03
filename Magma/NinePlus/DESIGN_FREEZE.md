# Design freeze — active 9+ exploration only

Status: 2026-11-03.

## EXPLICIT FREEZE: nine-round SAT motif hunting

The existing one-key parity collision and four-hot internal route
are retained as scientific fixtures. Both the exact CaDiCaL
and exact Z3 queries for the nominated full nine-round endpoint
`(0,0x00102402) -> (0,0x0080080a)` ended UNKNOWN at 600000 ms
per query. UNKNOWN is NOT impossibility.

No further large SAT runs, one-off witnesses, additional motif
certificates, or source-tree reshuffles in this branch until a
bottom-up exact join engine provides new *measured* reachability
information. Pure reproducibility fixes and tests against the
existing established local parity filter are allowed.

Next active work is **outside this frozen branch**:
`Magma/Composition/FOUNDATION_GAPS.md`, priority P0:
localize the 3-carry exact join; then exact fixed-key composition,
five-round regression, and only then 7/9+ exploration.


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

## Current path-level improvement (not an endpoint theorem)

A reusable one-bit-per-master-key parity transducer now rejects
all 740 additional pairs of output-support masks when two
reused-key g derivatives both have input difference 1.
Soundness is grounded in `ParityCollision.lean` and the already
kernel-proved even/odd support lists. The next gate is whether it
prunes actual longer-round DP paths after existing local filters.
The forced nine-round motif alone is **NOT** a proved impossible
endpoint differential. No more large SAT/Lean witness tables for it.

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
