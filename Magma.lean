module

public import Magma.RFC8891
public import Magma.CryptoProperties
public import Magma.CarryAutomaton
public import Magma.MultiRoundDDT
public import Magma.Pruning
public import Magma.Certificates
public import Magma.FastSearch
public import Magma.UInt8NoPathCertificates
public import Magma.OneHotCompleteSupport
public import Magma.OneHotKeyClasses
public import Magma.OneHotClassCertificates
public import Magma.OneHotCarryPrefix
public import Magma.OneHotSilentNibbleStructure
public import Magma.OneHotBoundaryReduction
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
