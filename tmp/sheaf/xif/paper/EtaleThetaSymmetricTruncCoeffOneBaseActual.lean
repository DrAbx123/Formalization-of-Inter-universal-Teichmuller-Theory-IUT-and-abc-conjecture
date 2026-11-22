import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffOneBaseActual

universe u

theorem etaleThetaSymmetricTrunc_one_coeff_one (K : Type u) [Field K] :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K 1).coeff
        (thetaQExponent 1) =
      HahnSeries.single (thetaUExponent 1) (-1 : K) +
        HahnSeries.single (thetaUExponent (-2)) (1 : K) := by
  rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_succ K 0]
  rw [HahnSeries.coeff_add]
  have h0 : (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm K 0).coeff (thetaQExponent 1) = 0 := by
    unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
      LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
    have hne : thetaQExponent 0 ≠ thetaQExponent 1 := by
      unfold thetaQExponent; norm_num
    have hne2 : thetaQExponent (-1) ≠ thetaQExponent 1 := by
      unfold thetaQExponent; norm_num
    simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne, hne2]
  rw [h0, zero_add]
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaQExponent, thetaUExponent]
  norm_num

#check etaleThetaSymmetricTrunc_one_coeff_one

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffOneBaseActual
