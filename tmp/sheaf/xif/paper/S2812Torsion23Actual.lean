import tmp.sheaf.xif.paper.S2811CoordStableActual
import Mathlib.FieldTheory.IsAlgClosed.Basic
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2790F6Actual
noncomputable section
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : IsAlgClosure S2790F6 S2790L :=
  { isAlgClosed := IsAlgClosure.isAlgClosed GaussianField
    isAlgebraic := inferInstance }

/-- A chosen isomorphism from AlgebraicClosure(F6) to AlgebraicClosure(Q(i)),
fixing F6. -/
noncomputable def S2812Equiv :
    AlgebraicClosure S2790F6 ≃ₐ[S2790F6] S2790L :=
  IsAlgClosure.equiv S2790F6 (AlgebraicClosure S2790F6) S2790L

/-- The remaining target: E[6] rational over F6. -/
def S2812Torsion23Target : Prop :=
  PuncturedEllipticCurve.Torsion23Rational (S2790E.baseChange S2790F6)

#check S2812Equiv
#check S2812Torsion23Target
end