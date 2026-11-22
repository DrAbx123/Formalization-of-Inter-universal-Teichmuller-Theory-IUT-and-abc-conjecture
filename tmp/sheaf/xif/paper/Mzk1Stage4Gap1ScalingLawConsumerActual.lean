import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual

/-! # Mzk1Stage4Gap1ScalingLawConsumerActual (stage4 lane; Gap1 scaling-law analysis)

A659 module: stage4 analysis/consumers of the GREEN target statement
`Mzk1Gap1ScalingLawTargetActual` (hull lane, READ only).  The product/`badInvScale`
scaling-law instantiation is still being written by hull; the target file shows that
under the exact scaling law Gap 1 is EQUIVALENT to an explicit arithmetic inequality
(no gap hidden), and the full-ratio case reduces to `log c <= (1+ε)·(...)`.  This file
records the blocking status and re-exports the reductions as thin consumers.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap1ScalingLawConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Consumer: exact scaling law + arithmetic inequality ⇒ Gap 1. -/
theorem stage4_gap1_of_law
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
  gap1_of_scalingLaw_and_arith T point ratio const ε hε hvol harith

/-- Consumer: under the scaling law, Gap 1 is exactly the arithmetic inequality. -/
theorem stage4_gap1_iff_arith
    (point : Nat → Nat → Nat → S1902Carrier T)
    (ratio : Nat → Nat → Nat → Real) (const ε : Real) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point ratio const) :
    (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + ε) *
            (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal) ↔
      (∀ a b c : Nat, IsABCTriple a b c →
        Real.log (c : Real) ≤
          (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
            Real.log (ratio a b c) + const)) :=
  gap1_arithmetic_condition_iff T point ratio const ε hε hvol

/-- Consumer: the FULL-ratio scaling law gives Gap 1 (unit volume and const nonneg). -/
theorem stage4_gap1_fullRatio
    (point : Nat → Nat → Nat → S1902Carrier T) (const ε : Real) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point FullRatio const)
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hconst : 0 ≤ const) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) *
          (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal :=
  gap1_of_fullRatio T point const ε hε hvol hunit hconst

/-- The blocking-status record for the Gap-1 scaling-law chain. -/
def blockingStatus : List (String × String) :=
  [ ("exact scaling law (PaperRegionScalingLaw)", "named hypothesis; product/badInvScale instantiation STILL BEING WRITTEN by hull (key blocking item)")
  , ("arithmetic reduction", "gap1_arithmetic_condition_iff: Gap 1 ⇔ explicit arithmetic inequality (no gap hidden)")
  , ("full-ratio favourable case", "ratio = a+b+c+1; Gap 1 reduces to log c <= (1+ε)(unit + log N + const)")
  , ("product law", "hull product law lemma (stage4 HullProductLawActual) supplies the measure-product step")
  , ("conclusion", "no paper conclusion changed; the remaining named content is the scaling law itself")
  ]

/-- The blocking-status record has five rows. -/
theorem blockingStatus_length : blockingStatus.length = 5 := rfl

#print axioms stage4_gap1_of_law
#print axioms stage4_gap1_iff_arith
#print axioms stage4_gap1_fullRatio

#check stage4_gap1_of_law
#check stage4_gap1_iff_arith
#check stage4_gap1_fullRatio
#check blockingStatus_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap1ScalingLawConsumerActual
end
