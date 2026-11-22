import tmp.sheaf.xif.paper.S1923UniversalB
import tmp.sheaf.xif.paper.S1923NormEDS232
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

open Universal

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

@[simp] lemma map_specialize : Universal.curve.map W.specialize = W := by
  ext <;> simp [specialize, Universal.curve]

namespace Universal

variable (x y : R)

def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]

@[simp] lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

@[simp] lemma ringEval_of_X : ringEval eqn (AdjoinRoot.of _ Polynomial.X) = x := by
  rw [← AdjoinRoot.mk_C, ringEval_mk, polyEval_apply]
  simp [Polynomial.evalEval]

@[simp] lemma ringEval_root : ringEval eqn (AdjoinRoot.root _) = y := by
  rw [← AdjoinRoot.mk_X, ringEval_mk, polyEval_apply]
  simp [Polynomial.evalEval]

end Universal
end WeierstrassCurve
