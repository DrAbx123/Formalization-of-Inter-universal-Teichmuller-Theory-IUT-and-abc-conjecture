import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
set_option relaxedAutoImplicit false
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveScheme3Actual
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev fermatGrading : Nat → Submodule ℚ (MvPolynomial (Fin 3) ℚ) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℚ
noncomputable def fermatProjectivePlane : Scheme :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := ℚ)
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ)
noncomputable def fermatPolynomial (n : Nat) : MvPolynomial (Fin 3) ℚ :=
  X 0 ^ n + X 1 ^ n - X 2 ^ n
theorem fermatPolynomial_isHomogeneous (n : Nat) :
    (fermatPolynomial n).IsHomogeneous n := by
  unfold fermatPolynomial
  exact (isHomogeneous_X_pow ..).add (isHomogeneous_X_pow ..) |>.sub (isHomogeneous_X_pow ..)
noncomputable def fermatClosedSubset (n : Nat) :
    Set (ProjectiveSpectrum fermatGrading) :=
  ProjectiveSpectrum.zeroLocus fermatGrading {fermatPolynomial n}
theorem fermatClosedSubset_isClosed (n : Nat) :
    IsClosed (fermatClosedSubset n) :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _
noncomputable def fermatProjectiveStructureMap :
    fermatProjectivePlane ⟶
      Spec (CommRingCat.of (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ 0)) :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := ℚ)
  AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ)
theorem fermatProjectivePlane_isProper :
    IsProper fermatProjectiveStructureMap := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := ℚ)
  infer_instance
#print axioms fermatPolynomial_isHomogeneous
#print axioms fermatProjectivePlane_isProper
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveScheme3Actual
end