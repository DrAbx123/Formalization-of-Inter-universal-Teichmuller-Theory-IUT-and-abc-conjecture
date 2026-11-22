import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.Algebra.Polynomial.Basic

noncomputable section
open LeanFormal.IUT
set_option autoImplicit false

#synth Algebra.FormallySmooth ℚ (Polynomial ℚ)
#synth Algebra.Smooth ℚ (Polynomial ℚ)
#synth Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Polynomial ℚ)
#synth RingHom.Smooth (algebraMap ℚ (Polynomial ℚ))
#synth RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap ℚ (Polynomial ℚ))

end
