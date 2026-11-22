import tmp.sheaf.xif.paper.S1533UniversalPointActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual

/-! # S1535: universal smulX/smulY and the exact recursion gap -/

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
namespace Universal
open MvPolynomial (X)

/-- Universal x-coordinate of n-multiplication: φ_n / ψ_n^2. -/
def smulX (n : ℤ) : Field :=
  polyToField (curve.toAffine.φ n) / (polyToField (curve.toAffine.ψ n)) ^ 2

/-- Universal y-coordinate of n-multiplication: ω_n / ψ_n^3. -/
def smulY (n : ℤ) : Field :=
  polyToField (curve.toAffine.ω n) / (polyToField (curve.toAffine.ψ n)) ^ 3

theorem smulX_def (n : ℤ) :
    smulX n = polyToField (curve.toAffine.φ n) /
      (polyToField (curve.toAffine.ψ n)) ^ 2 := rfl

theorem smulY_def (n : ℤ) :
    smulY n = polyToField (curve.toAffine.ω n) /
      (polyToField (curve.toAffine.ψ n)) ^ 3 := rfl

/-- Actual universal equation point (equation, not yet nonsingular point). -/
structure UniversalEquationPoint where
  x : Field
  y : Field
  equation : (curve.baseChange Field).toAffine.Equation x y

/-- The universal point from S1533. -/
def universalEquationPoint : UniversalEquationPoint where
  x := universalX
  y := universalY
  equation := universal_equation

/-- Exact missing: the smulX/smulY pair satisfies the base-changed equation. -/
def S1535SmulPointEquation (n : ℤ) : Prop :=
  (curve.baseChange Field).toAffine.Equation (smulX n) (smulY n)

/-- Exact missing recursion: n • universalPoint = (smulX n, smulY n).
  Stated as a Prop over the equation point because the nonsingular point/generic
  point recursion requires the ZSMul bridge, which is absent. -/
def S1535ZSMulRecursionMissing : Prop :=
  ∀ n : ℤ, S1535SmulPointEquation n

end Universal
end WeierstrassCurve
end