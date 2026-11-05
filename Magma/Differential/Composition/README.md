# Composition across round counts

To study a longer differential, the project joins shorter pieces through a common intermediate state. The central problem is to retain exactly the information needed for this join while reducing the cost of the calculation.

[JointTaggedAcceptance.lean](JointTaggedAcceptance.lean) provides a Magma-specific tagged transition identity. The [ROADMAP](Experiments/ROADMAP.md) and [FOUNDATION_GAPS](Experiments/FOUNDATION_GAPS.md) identify the corresponding proof and computational questions, and [COMPOSITIONALITY_DESIGN_FREEZE](Experiments/COMPOSITIONALITY_DESIGN_FREEZE.md) records the approaches deliberately paused. The [BDD experiments](Experiments/BDD/TWO_WORD_BDD.md) test whether compact encodings preserve the necessary information.

The concrete round-count implementations and results belong beside their target theorems in [FiveRounds](../FiveRounds/README.md), [SevenRounds](../SevenRounds/README.md), and [FullCipher](../FullCipher/README.md).
