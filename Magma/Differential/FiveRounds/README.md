# Five-round differential composition

A five-round trajectory couples the derivatives of several round functions through shared intermediate states. The question in this branch is whether the exact number of compatible trajectories can be recovered without replacing those shared states by independent local counts.

Start with [FiveRoundMiddleFiberMass.lean](FiveRoundMiddleFiberMass.lean), which formulates the exact middle-state sum. [FiveRoundLabelJoinDefect.lean](FiveRoundLabelJoinDefect.lean) describes what can go wrong when the middle state is replaced by a coarser label. The [tagged carry study](Experiments/TAGGED_TRANSFER.md) leads to [fixed-middle](Experiments/FIXED_MIDDLE_TRANSFER.md) and [joint-middle](Experiments/JOINT_MIDDLE_TRANSFER.md) counting experiments, alongside their Python/Rust implementations and recorded fixtures in [Experiments](Experiments).

The experiments establish concrete counts and compare computational methods; the Lean theorems establish the exact propositions they state. Their distinction and the next proof obligations are recorded in [FOUNDATION_GAPS](../Composition/Experiments/FOUNDATION_GAPS.md). Those results feed the [seven-round](../SevenRounds/README.md) and longer-window analyses.
