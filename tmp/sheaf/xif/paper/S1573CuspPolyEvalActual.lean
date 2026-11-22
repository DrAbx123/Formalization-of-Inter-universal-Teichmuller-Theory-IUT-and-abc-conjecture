import tmp.sheaf.xif.paper.S1530UniversalRingFieldActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
/-! # S1573: cusp specialization / polyEval actual; cusp psi evaluation exact stop
Ports the small structural layer: cusp curve on Z, specializeCusp, polyEvalCusp.
The TauCeti evaluation polyEval_cusp_psi remains the exact first missing; the
evaluation of psi2/Psi3/prePsi4 at the cusp needs a numeral/constant-coeff
normalization not present at v4.32.2 (or a direct polynomial computation).
ringEval is not defined yet.  No fake cusp and no assumed evaluation. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
/-- The cusp curve y^2 = x^3 over Z. -/
def cusp : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 0
theorem equation_cusp_one_one : cusp.toAffine.Equation 1 1 := by
  simp [cusp, WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.polynomial,
    Polynomial.evalEval_C, Polynomial.evalEval_X]
/-- Specialization of the universal coefficients at the cusp (all zero). -/
noncomputable def specializeCusp : MvPolynomial Coeff ℤ →+* ℤ :=
  MvPolynomial.eval (fun _ => 0)
/-- Evaluation of a universal bivariate polynomial at the cusp point (1,1). -/
noncomputable def polyEvalCusp : Universal.Poly →+* ℤ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom specializeCusp 1) 1
/-- Exact first missing: the cusp evaluates universal psi_n to n. -/
def S1573CuspPsiEval : Prop :=
  ∀ n : ℤ, polyEvalCusp (Universal.curve.ψ n) = n
-- Also missing: ringEval : Universal.Ring →+* Z and ringEval_mk, needed to
-- descend polyEvalCusp to the universal coordinate ring.  The injection
-- Universal.Ring -> Universal.Field then gives polyToField_psi_ne_zero as in
-- TauCeti Universal.lean.
#check S1573CuspPsiEval
#check polyEvalCusp
end WeierstrassCurve
