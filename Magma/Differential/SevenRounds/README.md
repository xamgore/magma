# Seven-round differential bounds

The five-round inner constraints can be combined with two outer rounds to test whether an input/output difference is impossible for every allowed sequence of keys. This branch studies those universal exclusions and the geometry of differences concentrated in particular nibbles.

[SevenTopNibbleImpossible.lean](SevenTopNibbleImpossible.lean) contains the high-nibble exclusion theorem; [SevenNibbleValuationClasses.lean](SevenNibbleValuationClasses.lean) develops the broader valuation classes. Their motivating computations and scope are described in [SEVEN_TOP_NIBBLE_THEOREM](Experiments/SEVEN_TOP_NIBBLE_THEOREM.md) and [NIBBLE_VALUATION_FAMILIES](Experiments/NIBBLE_VALUATION_FAMILIES.md). The separate [seven-core experiments](Experiments/SEVEN_CORE.md) study exact fixed-key composition and related solver checks.

For longer paths, the next problem is whether a certified forbidden seven-round edge actually removes a feasible intermediate transition. See [Windows](../Windows/README.md) and [NinePlus](../NinePlus/README.md).
