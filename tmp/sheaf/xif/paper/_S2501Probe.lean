import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
open AlgebraicGeometry
noncomputable section
abbrev G : ℕ → Submodule ℚ (MvPolynomial (Fin 2) ℚ) := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ
attribute [local instance] MvPolynomial.gradedAlgebra
#check AlgebraicGeometry.Proj
#check Proj
#check @AlgebraicGeometry.Proj.Proj
#check @Proj
