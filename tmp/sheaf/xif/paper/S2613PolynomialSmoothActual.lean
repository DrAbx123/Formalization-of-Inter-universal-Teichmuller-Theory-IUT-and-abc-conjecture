import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.Algebra.Polynomial.Basic

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2613PolynomialSmoothActual

/-- The actual affine model: `Polynomial ℚ` is smooth over `ℚ`.
`FormallySmooth.polynomial` is the actual Mathlib formal-smoothness instance;
`FinitePresentation` is the actual polynomial finite-presentation instance. -/
instance polynomialSmooth : Algebra.Smooth ℚ (Polynomial ℚ) where
  formallySmooth := Algebra.FormallySmooth.polynomial ℚ
  finitePresentation := inferInstance

/-- The corresponding ring hom is smooth. -/
theorem polynomial_algebraMap_smooth :
    RingHom.Smooth (algebraMap ℚ (Polynomial ℚ)) :=
  (RingHom.smooth_algebraMap).mpr inferInstance

#print axioms polynomial_algebraMap_smooth

end LeanFormal.IUT.XiFPaper.S2613PolynomialSmoothActual
end
