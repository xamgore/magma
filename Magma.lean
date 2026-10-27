module

public import Magma.RFC8891
public import Magma.CryptoProperties
public import Magma.CarryAutomaton
public import Magma.UnitInputParity
public import Magma.MultiRoundDDT
public import Magma.OddUnitInput77
public import Magma.Pruning
public import Magma.Certificates
public import Magma.FastSearch
public import Magma.UInt8NoPathCertificates
public import Magma.OneHot.CompleteSupport
public import Magma.OneHot.KeyClasses
public import Magma.OneHot.ClassCertificates
public import Magma.OneHot.CarryPrefix
public import Magma.OneHot.SilentNibbleStructure
public import Magma.OneHot.BoundaryReduction
public import Magma.OneHot.TraceSplit5
public import Magma.OneHot.PrefixArithmeticBridge
public import Magma.OneHot.FullKeyClassInvariant
public import Magma.OneHot.ThreeRoundColumns
public import Magma.OneHot.ExactColumnMass
public import Magma.OneHot.LinearPrefixMass
public import Magma.OneHot.QuantitativeTraceFactorization
public import Magma.OneHot.ExactCoefficientMasks
public import Magma.OneHot.GlobalMaximum
public import Magma.OneHot.FixedKeyPeak
public import Magma.OneHot.ActualKeyCardinality
public import Magma.OneHot.CompletePeakHistogram
public import Magma.OneHot.MaximizingBitMultiplicity
public import Magma.OneHot.JointPeakMultiplicity
public import Magma.OneHot.JointPeakMultiplicityHistogram
public import Magma.ZeroLeft.ColumnTransport
public import Magma.ZeroLeft.EightEntries
public import Magma.ZeroLeft.KeyParity
public import Magma.ZeroLeft.OddKey
public import Magma.BatchSearch
public import Magma.BatchFamily
import all Init.Data.Range.Basic

/-! Root module for the Magma specification and differential-analysis library. -/

-- set_option maxHeartbeats 5000
-- set_option maxRecDepth 100
-- set_option trace.profiler true
-- set_option trace.profiler.threshold 10
-- set_option diagnostics true
-- set_option diagnostics.threshold 100
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.synthInstance true

-- set_option trace.Meta.synthInstance false
-- set_option trace.Meta.isDefEq false
-- set_option diagnostics false
-- set_option trace.profiler false
