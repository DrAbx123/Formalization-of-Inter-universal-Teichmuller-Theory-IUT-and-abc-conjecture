import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# ShehddMatrixLogDetLawsConsumerActual — matrix log-determinant law bundle

STEP 0 prior-art (reuse only): HolomorphicHull/HullDeterminantLogVolumeReduction.lean:
matrixLogDet = log det; matrixLogDet_mul_posDef, matrixLogDet_smul_posDef,
matrixLogDet_kronecker_posDef, matrixLogDet_pow_posDef; packetDiagonalMatrix bridges
packets to matrices (packetLogVolume_eq_matrixLogDet).

This file packages the four matrix log-determinant laws (multiplicative, rescaling,
Kronecker/tensor, powers) as one consumer for the (Ob3-2)/(Ob3-3) determinant
bookkeeping.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddMatrixLogDetLawsConsumerActual

open LeanFormal.IUT
open scoped Kronecker

/-- **PROVED consumer bundle:** log-det is additive on positive definite factors,
rescales by n·log c, is additive on Kronecker products with cardinality weights, and
scales by M on natural powers. -/
theorem matrixLogDet_laws_consumer {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A B : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    (c : ℝ) (hc : 0 < c) (M : ℕ) :
    matrixLogDet (A * B) = matrixLogDet A + matrixLogDet B ∧
      matrixLogDet (c • A) =
        (Fintype.card m : ℝ) * Real.log c + matrixLogDet A ∧
      matrixLogDet (A ⊗ₖ C) =
        (Fintype.card n : ℝ) * matrixLogDet A +
          (Fintype.card m : ℝ) * matrixLogDet C ∧
      matrixLogDet (A ^ M) = (M : ℝ) * matrixLogDet A :=
  ⟨matrixLogDet_mul_posDef hA hB,
    matrixLogDet_smul_posDef c hc hA,
    matrixLogDet_kronecker_posDef hA hC,
    matrixLogDet_pow_posDef hA M⟩

/-- Row record: reused matrix log-det laws vs the consumer bundle. -/
def matrixLogDetRows : List (String × String × String) :=
  [ ("log-det = log det; additive on PosDef factors", "REUSED DEF/PROVED", "matrixLogDet / matrixLogDet_mul_posDef")
  , ("rescaling law n*log c", "REUSED PROVED", "matrixLogDet_smul_posDef")
  , ("Kronecker product law", "REUSED PROVED", "matrixLogDet_kronecker_posDef")
  , ("power law M*logDet", "REUSED PROVED", "matrixLogDet_pow_posDef")
  , ("consumer bundle", "COMPOSED PROVED", "matrixLogDet_laws_consumer") ]

theorem matrixLogDetRows_length : matrixLogDetRows.length = 5 := rfl

#check matrixLogDet_laws_consumer
#check matrixLogDetRows_length

end LeanFormal.IUT.XiFPaper.ShehddMatrixLogDetLawsConsumerActual
end
