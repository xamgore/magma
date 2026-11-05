# Differential analysis of Magma

[Magma's round function and key schedule](../RFC8891.lean) determine how a state changes. Differential analysis asks a different question: given a change in the input, which changes in the output are possible, and how many compatible states or keys realize them?

The analysis starts with a single round function, then follows differences through consecutive rounds. The difficulty changes with scale: local transition counts do not by themselves describe the correlations between the intermediate states of a longer trajectory. The directories below group the Lean theorems at each scale with the experiments that tested or motivated them.

| Scale / question | Start with | Computational investigations |
| --- | --- | --- |
| How does the round function transform differences? | [RoundFunction](RoundFunction/GBaseTaggedCarryStep.lean) | [XOR and modular differences](RoundFunction/Experiments/XOR_VS_MOD_REAL_MAGMA.md) |
| Which local support and DDT coefficients can be proved exactly? | [LocalDDT](LocalDDT), [DDT](../DDT) | [Numbered discovery iterations](../DDT/Experiments/README.md) |
| How do 2–3 rounds constrain compatible states? | [TwoRounds](TwoRounds), [ThreeRounds](ThreeRounds) | [Three-round carry tests](ThreeRounds/Experiments) |
| What information must a 4-round join preserve? | [FourRounds](FourRounds/FourRoundGeneralBoundaryEquations.lean) | [Related window probes](Windows/Experiments) |
| Can 5-round counts be composed exactly? | [FiveRounds](FiveRounds/README.md) | [Fixed and joint middle-state transfers](FiveRounds/Experiments/JOINT_MIDDLE_TRANSFER.md) |
| Which 7-round differential families vanish for every allowed key? | [SevenRounds](SevenRounds/README.md) | [Nibble valuation classification](SevenRounds/Experiments/NIBBLE_VALUATION_FAMILIES.md) |
| What happens at eight rounds and across arbitrary windows? | [EightRounds](EightRounds), [Windows](Windows/README.md) | [Sparse windows](Windows/Experiments/Sparse/SPARSE_WINDOWS.md) |
| Can linked keys and SAT constrain nine or more rounds? | [NinePlus](NinePlus/README.md) | [NinePlus research and results](NinePlus/Experiments/README.md) |
| How do reflected and repeated-key structures affect differences? | [Reflection](Reflection), [RepeatedKeys](RepeatedKeys) | [Reflection studies](Reflection/Experiments/REFLECTION_J_OPTIONS.md), [repeated-key studies](RepeatedKeys/Experiments/REPEATED_KEY_600S_STUDY.md) |
| What can be established for the full 32-round cipher? | [FullCipher](FullCipher/README.md) | [Half-zero composition](FullCipher/Experiments/HALF_ZERO_32_COMPOSITION.md), [observability tests](FullCipher/Experiments/FULL_32_ATTACK_GATE.md) |
| Which composition principles work across these scales? | [Composition](Composition/README.md), [Bridges](Bridges) | [Composition roadmap](Composition/Experiments/ROADMAP.md), [BDD tests](Composition/Experiments/BDD/TWO_WORD_BDD.md) |

## How the research developed

The chronology in Git shows why the scale of the questions changed. October 26–28 established the cipher model and one-round DDT structure. October 29–November 1 developed Difan composition laws and three-to-five-round joins. November 3 introduced reproducible SAT experiments on longer windows and explicit stopping criteria. November 4–5 added seven-round classifications, reflection identities and full-cipher composition studies. The original commits remain available through `git log` and `git log --follow -- <path>`; [the sparse-window chronology](Windows/Experiments/Sparse/archive/SPARSE_WINDOWS_HISTORY.md) retains earlier hypotheses as well as negative results.

Each study note states its question, model, result and next condition. A theorem, a replayed witness and a solver outcome support different claims; [proof policy](../PROOF_POLICY.md) explains those distinctions. A branch explicitly marked frozen remains available next to its code and results.
