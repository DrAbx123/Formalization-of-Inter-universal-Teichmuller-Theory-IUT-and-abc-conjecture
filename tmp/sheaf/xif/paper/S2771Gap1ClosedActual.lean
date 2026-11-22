import tmp.sheaf.xif.paper.S2769RankTwoTorsionBasisActual
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual

open LeanFormal.IUT

/-- Concrete label 5. -/
def S2771FiveLabel : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := by norm_num

/-- The algebraic-closure base change of the curve. -/
abbrev S2771W {F : Type*} [Field F] (X : PuncturedEllipticCurve F) :
    WeierstrassCurve (AlgebraicClosure F) :=
  X.curve.baseChange (AlgebraicClosure F)

/-- Gap 1 for an arbitrary once-punctured elliptic curve over a char-zero
field: its 5-torsion over the algebraic closure has a rank-two ZMod-5 basis. -/
theorem S2771_rankTwoTorsionBasis
    {F : Type*} [Field F] [CharZero F]
    (X : PuncturedEllipticCurve F) :
    Nonempty ((Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      X.LTorsion S2771FiveLabel) := by
  classical
  let W := S2771W X
  haveI : W.IsElliptic := inferInstance
  have h := S2769RankTwoTorsionBasisActual.S2769_rankTwoTorsionBasis
    (K := AlgebraicClosure F) W
  have hW : (S2771W X).toProjective =
      X.curve.toProjective.baseChange (AlgebraicClosure F) := rfl
  rw [hW] at h
  change Nonempty ((Fin 2 → ZMod 5) ≃ₗ[ZMod 5]
    ↥(AddSubgroup.torsionBy
      (X.curve.toProjective.baseChange (AlgebraicClosure F)).Point ((5 : ℕ) : ℤ)))
  exact h

#check S2771_rankTwoTorsionBasis
#print axioms S2771_rankTwoTorsionBasis

end LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
end
