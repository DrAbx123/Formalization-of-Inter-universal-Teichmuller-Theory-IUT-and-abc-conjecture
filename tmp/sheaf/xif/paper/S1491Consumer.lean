import tmp.sheaf.xif.paper.S1491NormEDSNetActual
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

open Polynomial WeierstrassCurve

/-! Consumer check: the target theorem is importable and yields the division-polynomial net. -/

#check IsEllipticNet.normEDS
#check IsEllipticSequence.normEDS
#check rel3_normEDS
#check rel3_special_normEDS

example {R : Type*} [CommRing R] (b c d : R) : IsEllipticNet (normEDS b c d) :=
  IsEllipticNet.normEDS b c d

example {F : Type*} [Field F] (W : WeierstrassCurve F) : IsEllipticNet W.ψ := by
  have h : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
  rw [h]
  exact IsEllipticNet.normEDS _ _ _

example {F : Type*} [Field F] (W : WeierstrassCurve F) (x y : F) :
    IsEllipticNet (fun n : ℤ => Polynomial.evalEval x y (W.ψ n)) := by
  have h : IsEllipticNet W.ψ := by
    have h' : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
    rw [h']
    exact IsEllipticNet.normEDS _ _ _
  have h2 := h.comp (Polynomial.evalEvalRingHom x y)
  simpa only [Function.comp_def, Polynomial.coe_evalEvalRingHom] using h2

example {F : Type*} [Field F] (W : WeierstrassCurve F) (x y : F) :
    IsEllipticSequence (fun n : ℤ => Polynomial.evalEval x y (W.ψ n)) :=
  IsEllipticNet.isEllipticSequence (by
    have h : IsEllipticNet W.ψ := by
      have h' : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
      rw [h']
      exact IsEllipticNet.normEDS _ _ _
    have h2 := h.comp (Polynomial.evalEvalRingHom x y)
    simpa only [Function.comp_def, Polynomial.coe_evalEvalRingHom] using h2)
