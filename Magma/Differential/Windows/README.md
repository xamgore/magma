# Differential windows

A differential condition can constrain a selected block of rounds without describing the entire encryption. This directory studies which boundary conditions survive, which intermediate states must remain correlated, and when a local exclusion can prune a longer path.

The Lean modules here give window intersections, key-schedule constraints and boundary reductions. The [sparse-window experiments](Experiments/Sparse/SPARSE_WINDOWS.md) explore restricted boundary differences, with the [earlier research log](Experiments/Sparse/archive/SPARSE_WINDOWS_HISTORY.md) preserved as a record of the tests and changes of direction. Shared [SAT tools](Experiments/SAT) contain input fixtures, a matrix runner and an independent verifier; their local, ignored runs are under `Experiments/SAT/runs/`.

The proof status of a short-window restriction must be read together with its endpoint assumptions. The [seven-round](../SevenRounds/README.md) and [nine-plus](../NinePlus/README.md) branches show how those restrictions are used at greater depth.
