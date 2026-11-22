import tmp.sheaf.xif.paper.S2809E6FiniteActual
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import Mathlib.FieldTheory.Normal.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2790F6Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2810F6GaloisTorsionActual

local instance s2810GaussianFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Conditional IsGalois: normal + char 0 separability. -/
theorem S2810_isGalois_of_normal
    (h : Normal GaussianField S2790F6) : IsGalois GaussianField S2790F6 := by
  haveI : Normal GaussianField S2790F6 := h
  haveI : FiniteDimensional GaussianField S2790F6 := S2809_finiteDimensional
  haveI : Algebra.IsIntegral GaussianField S2790F6 :=
    ⟨fun x => IsIntegral.of_finite GaussianField x⟩
  haveI : CharZero GaussianField := inferInstance
  haveI : Algebra.IsSeparable GaussianField S2790F6 :=
    Algebra.IsSeparable.of_integral (F := GaussianField) (K := S2790F6)
  exact IsGalois.mk

/-- The target that is still missing: E[6] rational over F6. -/
def S2810Torsion23Target : Prop :=
  PuncturedEllipticCurve.Torsion23Rational (S2790E.baseChange S2790F6)

#check S2810_isGalois_of_normal
#check S2810Torsion23Target

end LeanFormal.IUT.XiFPaper.S2810F6GaloisTorsionActual
end