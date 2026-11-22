import tmp.sheaf.xif.paper.Mzk1Stage4Gap1ScalingLawConsumerActual

/-! # Mzk1Stage4Gap1WiringActual (stage4 lane; Gap1 wiring to the paper ratio form)

A664 module: wiring of the GREEN target reduction (`Mzk1Gap1ScalingLawTargetActual`)
to the paper's ratio form for the ABC data: under the full-ratio scaling law and a
positive comparison-region log-volume, the pointwise Gap-1 inequality is equivalent to
the ratio bound `log c / (unit + log ratio + const) ≤ 1 + ε`.
No conclusion is changed; hypotheses are explicit.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap1WiringActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap1ScalingLawConsumerActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Wiring: under the full-ratio scaling law, the Gap-1 inequality gives the paper's
ratio bound at each ABC triple where the comparison-region log-volume is positive. -/
theorem stage4_abc_height_ratio
    (point : Nat → Nat → Nat → S1902Carrier T) (const ε : Real) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point FullRatio const)
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hconst : 0 ≤ const)
    {a b c : Nat} (habc : IsABCTriple a b c)
    (hden : 0 < (s1902LogVolume T (s1902UnitRegion T)).toReal +
      Real.log (FullRatio a b c) + const) :
    Real.log (c : Real) /
        ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          Real.log (FullRatio a b c) + const) ≤ 1 + ε := by
  have hg1 : Real.log (c : Real) ≤
      (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
    have h := stage4_gap1_fullRatio T point const ε hε hvol hunit hconst a b c habc
    rwa [abcRationalPoint_logHeight₁ habc] at h
  rw [div_le_iff₀ hden]
  calc Real.log (c : Real)
      ≤ (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal :=
        hg1
    _ = (1 + ε) *
          ((s1902LogVolume T (s1902UnitRegion T)).toReal +
            Real.log (FullRatio a b c) + const) := by rw [hvol a b c]

/-- Wiring in the reverse ratio direction: the ratio bound plus the scaling law gives
the pointwise Gap-1 bound (equivalence halves are re-exported from the target). -/
theorem stage4_abc_height_of_ratio
    (point : Nat → Nat → Nat → S1902Carrier T)
    (ratio : Nat → Nat → Nat → Real) (const ε : Real) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point ratio const)
    (harith : ∀ a b c : Nat, IsABCTriple a b c →
      Real.log (c : Real) ≤
        (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          Real.log (ratio a b c) + const)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) *
          (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal :=
  stage4_gap1_of_law T point ratio const ε hε hvol harith

#check stage4_abc_height_ratio
#check stage4_abc_height_of_ratio

end LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap1WiringActual
end
