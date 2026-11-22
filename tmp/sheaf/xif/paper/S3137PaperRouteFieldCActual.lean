import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.Audit.Status

/-! # S3137: paper-route field (c) hull/log-volume bridge data

INDEX.PAPER-ROUTE field (c) = regionVolume_le_normalizedWeight arithmetic side.
This records the constructible hull/log-volume part: given the actual hull
interface W, the comparison region is normalizedComparisonRegion W logShellPoint
and the theta bound is (W.logVolume W.hull).toReal; the weight side is the
production arithmeticWeight.  Constructible data only; the per-triple bound
remains INDEX.PAPER-ROUTE.region-volume-weight.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3137PaperRouteFieldCActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit

variable {X : Type} (W : IQHullLogVolumeInterface X)
variable (logShellPoint : Nat -> Nat -> Nat -> X)
variable (epsilon : Real)

/-- The paper-route comparison region (production normalizedComparisonRegion). -/
def paperRouteComparisonRegion : Nat -> Nat -> Nat -> Set X :=
  fun a b c => normalizedComparisonRegion W logShellPoint a b c

/-- The theta-pilot bound term of field (c): (W.logVolume W.hull).toReal. -/
def paperRouteThetaBound : Real :=
  (W.logVolume W.hull).toReal

/-- Field (c) shape recorded as a predicate: per-triple region log-volume bounded
by the normalized weight plus theta bound plus per-epsilon constant. -/
def paperRouteRegionVolumeWeightShape : Prop :=
  exists D : Real, forall a b c : Nat, IsABCTriple a b c ->
    (W.logVolume (paperRouteComparisonRegion W logShellPoint a b c)).toReal <=
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + paperRouteThetaBound W + D

/-- Constructible: the production region constructor factors through the
normalized comparison region definition (definitional equality). -/
theorem paperRouteComparisonRegion_eq :
    paperRouteComparisonRegion W logShellPoint =
      fun a b c => normalizedComparisonRegion W logShellPoint a b c :=
  rfl

end LeanFormal.IUT.XiFPaper.S3137PaperRouteFieldCActual

namespace LeanFormal.IUT.Audit

/-- INDEX: paper-route field (c) constructible hull data. -/
def INDEX_PAPER_ROUTE_fieldC : Obligation :=
  { id := "INDEX.PAPER-ROUTE.field-c-hull-data"
    source := "Cor312ToABCBridgeInterface.lean:200-251 (normalizedComparisonRegion, regionVolume_le_normalizedWeight); Cor312ComparisonGapReduction cor312Gap2_*; S3129 hull log-volume"
    status := VerificationStatus.interface
    note := "CONSTRUCTIBLE HULL HALF of field (c): paperRouteComparisonRegion = normalizedComparisonRegion W logShellPoint (production def, definitional); paperRouteThetaBound = (W.logVolume W.hull).toReal; paperRouteRegionVolumeWeightShape records the exact per-triple bound shape. Proved reductions in production: cor312Gap2_hull_logVolume_le_normalizedComparisonRegion, cor312Gap2_scaleShift_unitRegion_..., cor312Gap2_regionVolume_le_add_of_subadditive, cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound. REMAINING: actual point bound/dictionary instance (Cor312GapDictionaryLayer non-universality proved). Not ABC-strength."
    dependsOn := ["INDEX.PAPER-ROUTE.region-volume-weight"] }

end LeanFormal.IUT.Audit