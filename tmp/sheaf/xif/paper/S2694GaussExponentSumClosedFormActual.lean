import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2694GaussExponentSumClosedFormActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual

/-- The exact `GaussExponentSumClosedForm` statement of
`SignedAverageBoundActual`, reproduced locally because that module is blocked
upstream by `SourceTheaterLogVolumeSign`. -/
def S2694GaussExponentSumClosedForm (l : PrimeGeFive) : Prop :=
  (∑ j : SignedLabel l.value, (gaussExponent j.1).toNat) =
    (lStar l.value * (lStar l.value + 1) * (2 * lStar l.value + 1)) / 3

/-- At `l = 5` the closed form is the concrete identity `4+1+0+1+4 = 10`. -/
theorem S2694GaussExponentSumClosedForm_five :
    S2694GaussExponentSumClosedForm fiveLabel := by
  unfold S2694GaussExponentSumClosedForm
  have hreal : ((S2678GaussExponentSum (l := fiveLabel) : Nat) : Real) = 10 := by
    rw [S2678GaussExponentSum_cast]
    exact sourceThetaWeightSum_five
  have hnat : S2678GaussExponentSum (l := fiveLabel) = 10 := by
    exact_mod_cast hreal
  have hsum : (∑ j : SignedLabel fiveLabel.value,
      (gaussExponent j.1).toNat) = 10 := by
    simpa [S2678GaussExponentSum] using hnat
  rw [hsum]
  norm_num [fiveLabel, lStar]

/-- The `l = 5` signed-average coefficient is exactly `2 = 10/5`. -/
theorem S2694_coefficient_five :
    ((sourceThetaWeightSum fiveLabel : Real) /
      (c3ThetaCard (l := fiveLabel) : Real)) = 2 :=
  weightSum_div_card_five

/-- The actual signed average of the source-theater C3 at `l = 5` is `2 log 5`,
the concrete value of the signed hull average. -/
theorem S2694_signedAverage_five
    (I : OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := fiveLabel)
      (V := FinitePrimePlace 2 7) I) :
    (c3ThetaSignedProcession
        (actualSignedC3 (l := fiveLabel)
          (V := FinitePrimePlace 2 7) (I := I) D)).average =
      2 * Real.log 5 :=
  signedAverage_eq_two_log5 I D

#check S2694GaussExponentSumClosedForm_five
#check S2694_coefficient_five
#check S2694_signedAverage_five
#print axioms S2694GaussExponentSumClosedForm_five
#print axioms S2694_signedAverage_five

end LeanFormal.IUT.XiFPaper.S2694GaussExponentSumClosedFormActual
end
