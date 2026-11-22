import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveSchemeActual
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
/-- The homogeneous coordinate ring `Q[X0,X1,X2]` with its standard grading. -/
abbrev fermatGrading : Nat → Submodule ℚ (MvPolynomial (Fin 3) ℚ) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℚ
/-- The ambient projective plane `Proj Q[X0,X1,X2]` as an actual scheme. -/
noncomputable def fermatProjectivePlane : Scheme :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := ℚ)
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ)
/-- The Fermat polynomial `X0^n + X1^n - X2^n`. -/
noncomputable def fermatPolynomial (n : Nat) : MvPolynomial (Fin 3) ℚ :=
  X 0 ^ n + X 1 ^ n - X 2 ^ n
theorem fermatPolynomial_isHomogeneous (n : Nat) :
    (fermatPolynomial n).IsHomogeneous n := by
  unfold fermatPolynomial
  exact (isHomogeneous_X_pow ..).add (isHomogeneous_X_pow ..) |>.sub (isHomogeneous_X_pow ..)
/-- The actual Fermat closed subset of the projective plane. -/
noncomputable def fermatClosedSubset (n : Nat) :
    Set (ProjectiveSpectrum (fermatGrading (u := u))) :=
  ProjectiveSpectrum.zeroLocus (fermatGrading (u := u)) {fermatPolynomial n}
theorem fermatClosedSubset_isClosed (n : Nat) :
    IsClosed (fermatClosedSubset (u := u) n) :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _
theorem mem_fermatClosedSubset_iff (n : Nat)
    (P : ProjectiveSpectrum (fermatGrading (u := u))) :
    P ∈ fermatClosedSubset n ↔
      fermatPolynomial n ∈ P.asHomogeneousIdeal :=
  Iff.rfl
#print axioms fermatPolynomial_isHomogeneous
#print axioms fermatPolynomial_isHomogeneous
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveSchemeActual
end