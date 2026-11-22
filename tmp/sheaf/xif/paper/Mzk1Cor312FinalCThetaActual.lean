import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual

/-! # Mzk1Cor312FinalCThetaActual — C_Theta >= -1 consumer of the final assembly

A534 consumer module (no new mathematics): from the genuine Kummer realization and the
paper readout identifications (PaperKummerReading), derives the Corollary 3.12 constant
conclusion `C_Theta >= -1` for the calibration `thetaReading = C_Theta * |qReading|`, using
the already-proved strict volume comparison (`paperKummerReading_strict`) and
`paperKummerReading_CTheta`.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalCThetaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The paper q-pilot magnitude |log q| = -qReading is positive when qReading < 0. -/
theorem final_absLogQ_pos (R : PaperKummerReading T) (hqneg : R.qReading < 0) :
    0 < -R.qReading :=
  by linarith

/-- **Corollary 3.12 constant conclusion**: for the calibration
thetaReading = C_Theta * |log q|, the strict signed comparison gives -1 < C_Theta,
hence -1 <= C_Theta. -/
theorem final_cTheta_ge_neg_one (R : PaperKummerReading T) (hqneg : R.qReading < 0) :
    -1 <= R.thetaReading / (-R.qReading) := by
  have hstrict := paperKummerReading_strict T R
  have hqmag : (0 : Real) < -R.qReading := final_absLogQ_pos T R hqneg
  have hC : -1 < R.thetaReading / (-R.qReading) :=
    paperKummerReading_CTheta hqmag
      (by ring : R.qReading = -(-R.qReading))
      (by rw [div_mul_cancel₀ _ (neg_ne_zero.mpr (ne_of_lt hqneg))])
      hstrict
  exact le_of_lt hC

/-- The strict form of the constant conclusion. -/
theorem final_cTheta_gt_neg_one (R : PaperKummerReading T) (hqneg : R.qReading < 0) :
    -1 < R.thetaReading / (-R.qReading) := by
  have hstrict := paperKummerReading_strict T R
  have hqmag : (0 : Real) < -R.qReading := final_absLogQ_pos T R hqneg
  exact paperKummerReading_CTheta hqmag
    (by ring : R.qReading = -(-R.qReading))
    (by rw [div_mul_cancel₀ _ (neg_ne_zero.mpr (ne_of_lt hqneg))])
    hstrict

#check final_absLogQ_pos
#check final_cTheta_ge_neg_one
#check final_cTheta_gt_neg_one

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalCThetaActual
end
