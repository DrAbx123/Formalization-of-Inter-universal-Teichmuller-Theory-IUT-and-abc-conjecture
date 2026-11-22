import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Polynomial WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace ProbeAlg

theorem S1720SqrtPolynomial_map_ne_zero :
    S1720SqrtPolynomial.map (algebraMap ℚ S1720Field) ≠ 0 := by
  rw [Polynomial.map_ne_zero_iff (algebraMap ℚ S1720Field).injective]
  intro h
  have hdeg := S1720SqrtPolynomial_degree
  rw [h] at hdeg
  simp at hdeg

theorem S1687H_splits_in_F' : (S1687H.map (algebraMap ℚ S1720Field)).Splits := by
  have hf : ((S1687H * S1720SqrtPolynomial).map (algebraMap ℚ S1720Field)).Splits := by
    simpa [S1720H] using S1720H_splits
  rw [Polynomial.map_mul] at hf
  rw [Polynomial.splits_mul'] at hf
  exact hf.1.resolve_right S1720SqrtPolynomial_map_ne_zero

noncomputable def S1720Lift : S1687Field →ₐ[ℚ] S1720Field :=
  Polynomial.SplittingField.lift (f := S1687H) (L := S1720Field) S1687H_splits_in_F'

instance S1720Algebra : Algebra S1687Field S1720Field :=
  S1720Lift.toRingHom.toAlgebra

instance S1720Tower : IsScalarTower ℚ S1687Field S1720Field :=
  IsScalarTower.of_algebraMap_eq fun x => (S1720Lift.commutes x).symm

instance S1720Algebraic : Algebra.IsAlgebraic S1687Field S1720Field := by
  haveI : Algebra.IsIntegral S1687Field S1720Field := by
    refine ⟨fun x => ?_⟩
    exact IsIntegral.tower_top (A := S1687Field) (IsIntegral.of_finite ℚ x)
  infer_instance

end ProbeAlg
