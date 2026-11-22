import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Mzk1DetMatrixConsumerGlueActual — consumer corollaries of the matrix log-det laws

Small glue module (no new mathematics): combines the already-proved
`matrixLogDet_smul_posDef`, `matrixLogDet_pow_posDef`,
`matrixLogDet_kronecker_posDef` and `Matrix.PosDef.kronecker` into the consumer forms
used by the det bookkeeping.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1DetMatrixConsumerGlueActual

open LeanFormal.IUT

open scoped Kronecker

universe u

/-- Successive positive scalings: the two log terms add. -/
theorem matrixLogDet_smul_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) {c d : Real} (hc : 0 < c) (hd : 0 < d) :
    matrixLogDet (c • (d • A)) =
      (Fintype.card n : Real) * Real.log c +
        (Fintype.card n : Real) * Real.log d + matrixLogDet A := by
  rw [smul_smul, matrixLogDet_smul_posDef (c * d) (mul_pos hc hd) hA,
    Real.log_mul hc.ne' hd.ne']
  ring

/-- Positive scaling then a positive tensor power. -/
theorem matrixLogDet_pow_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) {c : Real} (hc : 0 < c) (M : Nat) :
    matrixLogDet ((c • A) ^ M) =
      (M : Real) * ((Fintype.card n : Real) * Real.log c + matrixLogDet A) := by
  rw [matrixLogDet_pow_posDef (hA.smul hc) M, matrixLogDet_smul_posDef c hc hA]
  ring

/-- Positive scaling of a Kronecker (tensor-packet) pair. -/
theorem matrixLogDet_kronecker_smul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m Real} {B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef)
    {c : Real} (hc : 0 < c) :
    matrixLogDet (c • (A ⊗ₖ B)) =
      ((Fintype.card m : Real) * (Fintype.card n : Real)) * Real.log c +
        (Fintype.card n : Real) * matrixLogDet A +
          (Fintype.card m : Real) * matrixLogDet B := by
  rw [matrixLogDet_smul_posDef c hc (hA.kronecker hB),
    matrixLogDet_kronecker_posDef hA hB, Fintype.card_prod]
  push_cast
  ring

/-- A positive tensor power of a Kronecker pair. -/
theorem matrixLogDet_kronecker_pow {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m Real} {B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef)
    (M : Nat) :
    matrixLogDet ((A ⊗ₖ B) ^ M) =
      (M : Real) * ((Fintype.card n : Real) * matrixLogDet A +
        (Fintype.card m : Real) * matrixLogDet B) := by
  rw [matrixLogDet_pow_posDef (hA.kronecker hB) M,
    matrixLogDet_kronecker_posDef hA hB]
  ring

#check matrixLogDet_smul_smul
#check matrixLogDet_pow_smul
#check matrixLogDet_kronecker_smul
#check matrixLogDet_kronecker_pow

end LeanFormal.IUT.XiFPaper.Mzk1DetMatrixConsumerGlueActual
end
