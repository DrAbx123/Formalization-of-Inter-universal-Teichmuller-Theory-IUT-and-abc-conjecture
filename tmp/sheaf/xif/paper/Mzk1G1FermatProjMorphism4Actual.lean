import tmp.sheaf.xif.paper.Mzk1G1FermatProjClosedSubscheme4Actual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjMorphism4Actual
open MvPolynomial AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveScheme4Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjClosedSubscheme4Actual
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The target projective line `P1 = Proj Q[U,V]`. -/
noncomputable def fermatP1 : Scheme :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := ℚ)
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
/-- Residual Fermat-to-P1 morphism data. -/
structure FermatToP1Morphism (n : Nat) where
  toP1 : fermatCurveScheme n ⟶ fermatP1
  isFinite : Prop
  degree : Nat
  degree_eq : degree = n ^ 2
def fermatToP1Missing (n : Nat) : Prop := Nonempty (FermatToP1Morphism n)
#print axioms fermatP1
#print axioms fermatToP1Missing
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjMorphism4Actual
end