import tmp.sheaf.xif.paper.Mzk1H5DetScalingLawsActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Mzk1DetNormalizationNumericsActual — numerical det-normalization factors

Small consumer module (no new mathematics): instantiates the proved scaling laws at the
concrete normalization data used by the IUT IV log-volume coefficient (p = 11, rank 2)
and derives the normalization *difference* factors.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1DetNormalizationNumericsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingLawsActual

/-- Normalization difference at rank 2, scaling by 11: `2 · log 11`. -/
theorem hull06_det_normalization_factor_eleven {A : Matrix (Fin 2) (Fin 2) Real}
    (hA : A.PosDef) :
    hull06MatrixLogDet ((11 : Real) • A) - hull06MatrixLogDet A =
      (2 : Real) * Real.log (11 : Real) := by
  have h := hull06_det_scaling (11 : Real) (by norm_num) hA
  linarith

/-- Iterated normalization at rank 2: an `M`-fold power multiplies the factor by `M`. -/
theorem hull06_det_normalization_factor_eleven_pow {A : Matrix (Fin 2) (Fin 2) Real}
    (hA : A.PosDef) (M : Nat) :
    hull06MatrixLogDet (((11 : Real) • A) ^ M) - hull06MatrixLogDet A =
      (M : Real) * ((2 : Real) * Real.log (11 : Real)) := by
  rw [hull06_det_pow (hA.smul (by norm_num)) M]
  have h := hull06_det_scaling (11 : Real) (by norm_num) hA
  linarith

/-- Matrix-level normalization difference at rank 2, scaling by 11. -/
theorem matrixLogDet_normalization_factor_eleven {A : Matrix (Fin 2) (Fin 2) Real}
    (hA : A.PosDef) :
    matrixLogDet ((11 : Real) • A) - matrixLogDet A =
      (2 : Real) * Real.log (11 : Real) := by
  have h := matrixLogDet_smul_posDef (11 : Real) (by norm_num) hA
  linarith

/-- Tensor-packet normalization at rank `2 × 2`: the Kronecker factor sum. -/
theorem matrixLogDet_kronecker_normalization_eleven {A B : Matrix (Fin 2) (Fin 2) Real}
    (hA : A.PosDef) (hB : B.PosDef) :
    matrixLogDet (A ⊗ₖ B) =
      (2 : Real) * matrixLogDet A + (2 : Real) * matrixLogDet B := by
  rw [matrixLogDet_kronecker_posDef hA hB]
  norm_num

#check hull06_det_normalization_factor_eleven
#check hull06_det_normalization_factor_eleven_pow
#check matrixLogDet_normalization_factor_eleven
#check matrixLogDet_kronecker_normalization_eleven

end LeanFormal.IUT.XiFPaper.Mzk1DetNormalizationNumericsActual
end
