import Mathlib
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual

/-! # S3131 paper route: (b) height reduction — UNDILATED dictionary bound implies (b)

The (1+eps) dilation in (b) is bookkeeping once the log-volume is nonnegative:
this file proves (b) from the UNDILATED height/dictionary bound, which is the
form the hull canonical readout (MissingConcreteVFormCanonicalReadout) and the
sourceLocalLogDegree dictionary files can feed. -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual

universe u

/-- UNDILATED height bound: the exact dictionary input needed for (b). -/
def UndilatedHeightBound {X : Type u} (W : IQHullLogVolumeInterface X)
    (pt : Nat → Nat → Nat → X) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (W.logVolume {pt a b c}).toReal

/-- **PROVABLE reduction:** the undilated bound implies field (b). -/
theorem heightComparisonFamily_of_undilated {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : UndilatedHeightBound W pt) : HeightComparisonFamily W pt := by
  intro eps heps a b c habc
  have h1 := h a b c habc
  have hv : (0 : Real) ≤ (W.logVolume {pt a b c}).toReal := ENNReal.toReal_nonneg
  have hdil : (W.logVolume {pt a b c}).toReal ≤ (1 + eps) * (W.logVolume {pt a b c}).toReal :=
    by nlinarith [hv, heps]
  linarith

#check heightComparisonFamily_of_undilated

end LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
end