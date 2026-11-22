import tmp.sheaf.xif.paper.S2679PaperHcompNormalizationActual
import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2696SignedHullVBadAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2679PaperHcompNormalizationActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual

/-- The concrete prime label `l = 5`. -/
def S2696FiveLabel : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

/-- The actual Gauss sum at `l = 5` is `4+1+0+1+4 = 10` (kernel `decide` over
`ZMod 5`, no `native_decide`). -/
theorem S2696_gaussianExponentSum_five :
    gaussianExponentSum S2696FiveLabel = 10 := by
  unfold gaussianExponentSum
  have hnat : (∑ j : SignedLabel S2696FiveLabel.value,
      (gaussExponent j.1).toNat) = 10 := by
    rw [Fintype.sum_equiv (SignedLabel.equiv S2696FiveLabel)
      (fun j : SignedLabel S2696FiveLabel.value => (gaussExponent j.1).toNat)
      (fun x : Fl S2696FiveLabel.value =>
        (gaussExponent ((SignedLabel.equiv S2696FiveLabel).symm x).1).toNat)
      (by intro j; rw [Equiv.symm_apply_apply])]
    decide
  exact hnat

/-- The coefficient at `l = 5` is exactly `2 = 10/5`. -/
theorem S2696_gaussianCoefficient_five :
    gaussianCoefficient S2696FiveLabel = 2 := by
  unfold gaussianCoefficient
  rw [S2696_gaussianExponentSum_five]
  change 10 / (Fintype.card (SignedLabel S2696FiveLabel.value) : Real) = 2
  rw [SignedLabel.card_signedLabel S2696FiveLabel]
  norm_num [S2696FiveLabel]

/-- Paper q-pilot ray inclusion `qPilotLogVolume ∈ R_{≤ signedHullLogVolume}` is
exactly `2 ≤ S1527OrderC3` for any signed hull whose raw procession average is
`2 log 5`.  This is the hcomp object (ray inclusion), not the C_Theta-normalized
IUT IV average. -/
theorem S2696_paperInput_qPilotRay_iff_two_le_order
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5) :
    (S1895PaperO D).qPilotLogVolume ∈
        hullLogVolumeRay P.signedHullLogVolume ↔
      2 ≤ S1527OrderC3 := by
  rw [mem_hullLogVolumeRay_iff,
    PaperSignedHull.signedHullLogVolume_eq_neg_average P, hP]
  have hq : (S1895PaperO D).qPilotLogVolume =
      -(sourceBadQAbsLog (S1895PaperInput.I D).initial) := by
    rw [← neg_s1895PaperO_qPilotLogVolume D]
    ring
  rw [hq, paperInput_sourceBadQAbsLog D]
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have h' : (2 : Real) ≤ (S1527OrderC3 : Real) := by nlinarith
    exact_mod_cast h'
  · intro h
    have h' : (2 : Real) ≤ (S1527OrderC3 : Real) := by exact_mod_cast h
    nlinarith

/-- The same ray-inclusion criterion in the RHS form used by
`concreteSourceComparison`: `2 log 5 ≤ order_C3 log 5`. -/
theorem S2696_paperInput_qPilotRay_iff_comparison
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5) :
    (S1895PaperO D).qPilotLogVolume ∈
        hullLogVolumeRay P.signedHullLogVolume ↔
      paperSourceComparison (S1895PaperO D) P := by
  rw [S2696_paperInput_qPilotRay_iff_two_le_order D P hP,
    paperSourceComparison_s1895PaperO_iff D P,
    paperInput_sourceBadQAbsLog D, hP]
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have h' : (2 : Real) ≤ (S1527OrderC3 : Real) := by exact_mod_cast h
    nlinarith
  · intro h
    have h' : (2 : Real) ≤ (S1527OrderC3 : Real) := by nlinarith
    exact_mod_cast h'

#check S2696_gaussianCoefficient_five
#check S2696_paperInput_qPilotRay_iff_two_le_order
#check S2696_paperInput_qPilotRay_iff_comparison
#print axioms S2696_paperInput_qPilotRay_iff_two_le_order

end LeanFormal.IUT.XiFPaper.S2696SignedHullVBadAlignmentActual
end
