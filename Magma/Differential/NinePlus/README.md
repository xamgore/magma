# Nine rounds and beyond

Beyond eight rounds, the project tests whether sparse boundary conditions, repeated keys and correlated intermediate states can rule out additional differential transitions. This requires distinguishing a feasible local derivative from a full trajectory under the actual key schedule.

The Lean modules contain the scheduled nine-round model, reflection results and checked positive examples. The [research notes](Experiments/README.md) connect hypotheses with executable SAT/Z3 experiments, input fixtures and independently replayed results. Bulk one-hot positive certificates are stored in [PositiveRows](PositiveRows) and remain opt-in rather than part of the default library build.

The branch's [DESIGN_FREEZE](Experiments/DESIGN_FREEZE.md) states which large searches were stopped, why their existing results remain useful and what measured improvement would justify returning to them. Related exact joins are developed in [FiveRounds](../FiveRounds/README.md) and [Composition](../Composition/README.md).
