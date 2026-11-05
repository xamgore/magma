# Diffan

The project studies how differences between cipher states behave under successive transformations. To reason about several rounds, we first need definitions that do not depend on a particular round function: what a difference is, how it is measured from a base state, and how constraints on intermediate states can be combined. These definitions and their consequences form the Diffan library.

The modules follow that progression:

| Step | Modules | What they establish |
| --- | --- | --- |
| 1. Describe differences | [Core](Core/DifferenceSpace.lean) | Difference spaces, differential maps, state and parameter constraints |
| 2. Describe trajectories | [Paths](Paths/Chain.lean) | Chains of compatible transitions, path counts and reversal |
| 3. Compose trajectories | [Composition](Composition/ExactBaseJoin.lean) | Exact joins through shared states and scheduled parameters |
| 4. Retain sufficient information | [Fibers](Fibers/MiddleObservation.lean) | Fiber masses, observations, graph-supported joins and their limitations |
| 5. Compute and certify | [Algorithms](Algorithms/WeightedKernel.lean) | Weighted kernels, finite transfers and certified pruning |
| 6. Study structure | [Symmetry](Symmetry/ReflectedMacroSchedule.lean) | Translation, reflection, conjugacy and their invariants |
| 7. Interpret measurable quantities | [Observables](Observables/SlicedCollisionEnergy.lean) | Walsh correlations, collision statistics and observable constraints |

[Diffan.lean](../Diffan.lean) is the library entry point. The corresponding theorems for the actual Magma round function and schedule are organized under [Magma/Differential](../Magma/Differential/README.md).
