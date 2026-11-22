import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import tmp.sheaf.xif.paper.Node09RegionMonoActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Node09RegionMonoActual

namespace LeanFormal.IUT.XiFPaper.Node09Gap2SourceActual

universe u

/-- The source-data named ENNReal estimate (SNamed on the comparison region)
implies the singleton point-volume bound, hence hpoint, with hull absorbed. -/
theorem hpoint_of_SNamed
    {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) {eps D : Real}
    (hS : ∀ a b c : Nat, IsABCTriple a b c →
      SNamed (W.logVolume (normalizedComparisonRegion W logShellPoint a b c))
        eps (arithmeticWeight (abcRationalPoint a c))
        (W.logVolume W.hull).toReal D)
    (hR : ∀ a b c : Nat, IsABCTriple a b c →
      0 ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D)
    (hfin : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) < ⊤) :
    ∃ D1 : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1 := by
  refine ⟨(W.logVolume W.hull).toReal + D, fun a b c habc => ?_⟩
  have hregion : (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D :=
    gap2_real_bound (hR a b c habc) (hS a b c habc)
  have hmono : W.logVolume {W.scaleShift (logShellPoint a b c)} ≤
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) :=
    singletonVolume_le_regionVolume X W logShellPoint a b c
  have hle : (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
    ENNReal.toReal_mono (ne_of_lt (hfin a b c habc)) hmono
  calc (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal
      ≤ (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal := hle
    _ ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D := hregion
    _ = (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((W.logVolume W.hull).toReal + D) := by ring

/-- Exact source-data requirement for frozen gap2. -/
def Node09Gap2SourceResidual : List String :=
  [ "SNamed regionVolume eps weight theta D is the named ENNReal analytic estimate (Mzk1ABCBridgeGap2ConsumerActual.SNamed): regionVolume <= ofReal ((1+eps)*weight + theta + D)",
    "for the comparison region this is exactly the frozen gap2 regionVolume_le_normalizedWeight in ENNReal form; gap2_real_bound/gap2_ennreal_bound convert between the two",
    "hpoint_of_SNamed shows that a source-data SNamed family plus nonnegativity and region finiteness yields the singleton point-volume bound (hull absorbed into D1)",
    "no producer of SNamed exists in the tree; it remains the paper-level IUT IV main log-volume estimate and must be supplied as source data, no fake" ]

end LeanFormal.IUT.XiFPaper.Node09Gap2SourceActual
