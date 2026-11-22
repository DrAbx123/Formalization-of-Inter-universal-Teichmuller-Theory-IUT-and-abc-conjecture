import Mathlib.RingTheory.Flat.Localization
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct

namespace ABCBridge.JKFinalCoefficient
universe u
variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (t : ι → R)

abbrev chartRing (i : ι) : Type u := Localization.Away (t i)
abbrev overlapRing (i j : ι) : Type u := Localization.Away (t i * t j)
abbrev chartFixed (i : ι) : Type u :=
  FixedPoints.subalgebra (chartRing (R := R) (t := t) i)
    (chartRing (R := R) (t := t) i ⊗[R] A) G
abbrev overlapFixed (i j : ι) : Type u :=
  FixedPoints.subalgebra (overlapRing (R := R) (t := t) i j)
    (overlapRing (R := R) (t := t) i j ⊗[R] A) G

/-- The M1 equivalence at the overlap. -/
noncomputable def overlapFixedEquiv (i j : ι) :
    overlapRing (R := R) (t := t) i j ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[overlapRing (R := R) (t := t) i j]
      overlapFixed (R := R) (A := A) (G := G) (t := t) i j :=
  letI : Module.Flat R (overlapRing (R := R) (t := t) i j) :=
    IsLocalization.flat (overlapRing (R := R) (t := t) i j) (Submonoid.powers (t i * t j))
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := overlapRing (R := R) (t := t) i j)

/-- Pure-tensor coefficient for the M1 overlap equivalence. -/
theorem overlapFixedEquiv_coe_tmul (i j : ι)
    (b : overlapRing (R := R) (t := t) i j) (a : FixedPoints.subalgebra R A G) :
    ((overlapFixedEquiv (R := R) (A := A) (G := G) t i j (b ⊗ₜ[R] a) :
        overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
        overlapRing (R := R) (t := t) i j ⊗[R] A) =
      b ⊗ₜ[R] (a : A) := by
  simp [overlapFixedEquiv, M1Final.tensorFixedPointsAlgEquiv,
    AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]


/-- Round-trip identity for the M1 overlap equivalence. -/
theorem overlapFixedEquiv_apply_symm (i j : ι)
    (x : overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
    overlapFixedEquiv (R := R) (A := A) (G := G) t i j
        ((overlapFixedEquiv (R := R) (A := A) (G := G) t i j).symm x) = x :=
  (overlapFixedEquiv (R := R) (A := A) (G := G) t i j).apply_symm_apply x

/-- Induction principle for the overlap fixed-point subalgebra using M1. -/
theorem overlapFixed_induction (i j : ι)
    {P : overlapFixed (R := R) (A := A) (G := G) (t := t) i j → Prop}
    (h : ∀ y : overlapRing (R := R) (t := t) i j ⊗[R] FixedPoints.subalgebra R A G,
      P (overlapFixedEquiv (R := R) (A := A) (G := G) t i j y)) :
    ∀ x, P x := by
  intro x
  rw [show x = overlapFixedEquiv (R := R) (A := A) (G := G) t i j
      ((overlapFixedEquiv (R := R) (A := A) (G := G) t i j).symm x) from
    ((overlapFixedEquiv (R := R) (A := A) (G := G) t i j).apply_symm_apply x).symm]
  exact h ((overlapFixedEquiv (R := R) (A := A) (G := G) t i j).symm x)

end ABCBridge.JKFinalCoefficient