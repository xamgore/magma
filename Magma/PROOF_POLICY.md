# Proof triage policy (Magma/Difan)

## Three kinds of evidence: never conflate them

| Label | Meaning | Storage | What may be claimed |
|---|---|---|---|
| **Lean theorem** | Kernel checked; no `sorry` or unproved `axiom` | `Magma/Differential/**/*.lean` | Exactly the theorem as stated |
| **Verified SAT witness** | A complete key/base model directly replayed | compressed matrix + Rust/Python verifier | Existence for that one pair and key |
| **UNSAT experiment** | Solver says the encoded relation is empty | reproducible solver + parameters + logs | Computational evidence; no Lean theorem |
| **Hypothesis** | Candidate general pattern or conditional application | research note | Possible next experiment, not a result |

For Z3 `unsat`, explicitly document the relaxation and solver
timeout. If the relation is an overapproximation, a reliable UNSAT
implies a true impossibility **semantically**, but without a proof
certificate it still depends on the encoding and solver.

## First ask: what does the result buy?

Every proposed formalization should answer:

1. **Novelty:** Is this a reusable identity/invariant/search method,
   or just a concrete witness/finite table?
2. **Use:** Which later theorem, family of keys, or multi-round
   search will consume it? Give an actual named downstream cut.
3. **Gain:** What is eliminated beyond the existing filters? Measure
   the delta with a controlled computational experiment.
4. **Cost:** Can we first state the needed property as a `Prop`,
   prove a conditional theorem taking that property as a hypothesis,
   and defer its certification?
5. **Stop condition:** If the new filter prunes no additional paths
   or fails to generalize, archive the experiment and stop.

A lemma with no downstream application or tested gain should not
automatically enter the root library.

## Recommended workflow

```text
observation
  -> one-page research note
  -> computational A/B test against existing baseline
  -> named abstract Prop and optional soundness theorem
  -> actual downstream application (longer-round exclusion / DP gain)
  -> compact kernel-checkable certificate ONLY if worthwhile
```

For an expensive finite claim, prefer `def Candidate : Prop` and
a theorem `(h : Candidate) -> Consequence`. This cleanly separates
**conditional mathematical consequences** from **unproved facts**.
Do not silently turn a hypothesis into an `axiom` or `sorry`.

Positive reachability is already existential; direct independent
replay of solver witnesses is generally enough for exploration.
Formalize bulk positives only to settle a genuinely interesting
universal quantified claim or unblock a central proof.

## Repository structure and low-friction builds

- Default `lake build Magma`: core reusable theory and certified
  soundness properties, without mass proof-of-witness datasets.
- Opt-in `lake build Magma.Differential.NinePlus.Certificates`: bulk positive
  nine-round one-hot witness proofs (still tracked, not deleted).
- `Magma/Differential/Windows/Experiments/Sparse/SPARSE_WINDOWS.md`: current high-signal research map.
- `Magma/Differential/Windows/Experiments/Sparse/archive/SPARSE_WINDOWS_HISTORY.md`: detailed
  chronological experiments, preserved for provenance.
- `Magma/Differential/**/Experiments/**/*.rs` and `Magma/Differential/**/Experiments/**/*.py`: reproducible explorations
  and independent model replays; outputs stay ignored by Git.

Prefer semantic separation of executable research, reusable Lean
theory and generated evidence. When moving a research branch, keep module imports, command paths,
generators, fixtures and independent replay tools synchronized; an
organizational refactor is complete only after checking the affected
proof and experiment entry points.

## Current decision (2026-11-03)

The 1024 nine-round positive Lean certificates are **closed and
opt-in**. No new bulk proof generation unless it supports a more
general theorem.

Eight-round local-support Z3 experiments are **open**. Existing Lean
soundness and symmetry results are worth retaining, but the three
remaining UNSAT certificates are **not yet worth an expensive formal
campaign** until an experiment demonstrates useful improvement in
longer-round searches.

Prioritize reusable key/base-correlated transducers and sharp
round-boundary theorems over concrete special cases.
