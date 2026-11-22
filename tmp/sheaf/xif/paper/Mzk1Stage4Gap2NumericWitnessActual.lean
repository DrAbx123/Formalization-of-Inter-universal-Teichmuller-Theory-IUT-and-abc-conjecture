import tmp.sheaf.xif.paper.Mzk1Stage4Gap2ConsumerActual

/-! # Mzk1Stage4Gap2NumericWitnessActual (stage4 lane; unique filename)

A574 module: concrete numeric witness for the Gap1+Gap2 height bound consumer
(Stage4Gap2Consumer): with height = 1, region volume = 2, weight = 1, eps = 1/10,
hull = 5, D = 0, the height bound holds with A = 5.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2NumericWitnessActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ConsumerActual

/-- Numeric Gap witness: the two-gap data at the concrete numbers yields an
additive constant. -/
theorem gap2_numeric_witness :
    ∃ A : Real, (1 : Real) <= (1 + 1 / 10) * 1 + A :=
  height_bound_of_gaps (height := 1) (regionVol := 2) (weight := 1)
    (eps := 1 / 10) (hull := 5) (D := 0)
    (by norm_num) (by norm_num)

/-- Numeric witness with an explicit nonnegative constant A = 5. -/
theorem gap2_numeric_witness_nonneg :
    ∃ A : Real, 0 <= A ∧ (1 : Real) <= (1 + 1 / 10) * 1 + A :=
  height_bound_of_gaps_nonneg (height := 1) (regionVol := 2) (weight := 1)
    (eps := 1 / 10) (hull := 5) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The witness constant A = 5 works. -/
theorem gap2_numeric_witness_five : (1 : Real) <= (1 + 1 / 10) * 1 + 5 := by
  norm_num

#check gap2_numeric_witness
#check gap2_numeric_witness_nonneg
#check gap2_numeric_witness_five

end LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2NumericWitnessActual
end
