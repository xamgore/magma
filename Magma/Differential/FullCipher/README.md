# Full-cipher properties

The actual RFC 8891 encryption consists of 32 rounds with a particular repeated and reversed key schedule. This branch asks which relations can be proved for that complete permutation, and which of those relations yield a quantity accessible through a stated observation model.

[FullScheduleConjugacy.lean](FullScheduleConjugacy.lean) formalizes the key-schedule structure, while [Full32SlicedJoin.lean](Full32SlicedJoin.lean) studies exact composition across two half-cipher blocks. The [full-schedule study](Experiments/FULL_SCHEDULE_REFLECTION.md) explains the resulting identities. [HALF_ZERO_32_COMPOSITION](Experiments/HALF_ZERO_32_COMPOSITION.md) examines projections of exact differential sums; [FULL_32_ATTACK_GATE](Experiments/FULL_32_ATTACK_GATE.md) separates algebraic properties from an observable distinguisher.

Further work depends on preserving the full middle-state relation or proving a sound reduction of it. Current experiments and rejected shortcuts remain in [Experiments](Experiments), with their decisions recorded in [Composition's design freeze](../Composition/Experiments/COMPOSITIONALITY_DESIGN_FREEZE.md).
