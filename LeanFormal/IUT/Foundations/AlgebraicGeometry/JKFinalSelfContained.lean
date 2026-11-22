import Mathlib.RingTheory.Flat.Localization
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct

namespace ABCBridge.JKFinalSelfContained
universe u
variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (t : ι → R)

abbrev chartRing (i : ι) : Type u := Localization.Away (t i)
abbrev overlapRing (i j : ι) : Type u := Localization.Away (t i * t j)
abbrev tripleRing (i j k : ι) : Type u := Localization.Away (t i * t j * t k)
abbrev chartFixed (i : ι) : Type u :=
  FixedPoints.subalgebra (chartRing (R := R) (t := t) i)
    (chartRing (R := R) (t := t) i ⊗[R] A) G
abbrev overlapFixed (i j : ι) : Type u :=
  FixedPoints.subalgebra (overlapRing (R := R) (t := t) i j)
    (overlapRing (R := R) (t := t) i j ⊗[R] A) G
abbrev tripleFixed (i j k : ι) : Type u :=
  FixedPoints.subalgebra (tripleRing (R := R) (t := t) i j k)
    (tripleRing (R := R) (t := t) i j k ⊗[R] A) G

noncomputable def m1Overlap (i j : ι) :
    overlapRing (R := R) (t := t) i j ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[overlapRing (R := R) (t := t) i j]
      overlapFixed (R := R) (A := A) (G := G) (t := t) i j :=
  letI : Module.Flat R (overlapRing (R := R) (t := t) i j) :=
    IsLocalization.flat (overlapRing (R := R) (t := t) i j) (Submonoid.powers (t i * t j))
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := overlapRing (R := R) (t := t) i j)

noncomputable def m1Triple (i j k : ι) :
    tripleRing (R := R) (t := t) i j k ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[tripleRing (R := R) (t := t) i j k]
      tripleFixed (R := R) (A := A) (G := G) (t := t) i j k :=
  letI : Module.Flat R (tripleRing (R := R) (t := t) i j k) :=
    IsLocalization.flat (tripleRing (R := R) (t := t) i j k)
      (Submonoid.powers (t i * t j * t k))
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := tripleRing (R := R) (t := t) i j k)

theorem m1Overlap_coe_tmul (i j : ι)
    (b : overlapRing (R := R) (t := t) i j) (a : FixedPoints.subalgebra R A G) :
    ((m1Overlap (R := R) (A := A) (G := G) t i j (b ⊗ₜ[R] a) :
        overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
        overlapRing (R := R) (t := t) i j ⊗[R] A) =
      b ⊗ₜ[R] (a : A) := by
  simp [m1Overlap, M1Final.tensorFixedPointsAlgEquiv,
    AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]

theorem m1Overlap_apply_symm (i j : ι)
    (x : overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
    m1Overlap (R := R) (A := A) (G := G) t i j ((m1Overlap (R := R) (A := A) (G := G) t i j).symm x) = x :=
  (m1Overlap (R := R) (A := A) (G := G) t i j).apply_symm_apply x

theorem overlapFixed_induction (i j : ι)
    {P : overlapFixed (R := R) (A := A) (G := G) (t := t) i j → Prop}
    (h : ∀ y : overlapRing (R := R) (t := t) i j ⊗[R] FixedPoints.subalgebra R A G,
      P (m1Overlap (R := R) (A := A) (G := G) t i j y)) :
    ∀ x, P x := by
  intro x
  rw [show x = m1Overlap (R := R) (A := A) (G := G) t i j
      ((m1Overlap (R := R) (A := A) (G := G) t i j).symm x) from
    ((m1Overlap (R := R) (A := A) (G := G) t i j).apply_symm_apply x).symm]
  exact h ((m1Overlap (R := R) (A := A) (G := G) t i j).symm x)


noncomputable def overlapToTripleBase (i j k : ι) : overlapRing (R := R) (t := t) i j →ₐ[R] tripleRing (R := R) (t := t) i j k :=
  { toRingHom := IsLocalization.Away.awayToAwayRight (t i * t j) (t k)
    commutes' := fun r => by
      change IsLocalization.Away.awayToAwayRight (t i * t j) (t k)
        (algebraMap R (overlapRing (R := R) (t := t) i j) r) = algebraMap R (tripleRing (R := R) (t := t) i j k) r
      exact IsLocalization.Away.awayToAwayRight_eq (t i * t j) (t k) r }

noncomputable def overlapToTriple (i j k : ι) :
    overlapFixed (R := R) (A := A) (G := G) (t := t) i j →ₐ[R]
      tripleFixed (R := R) (A := A) (G := G) (t := t) i j k := by
  letI : Algebra (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k) :=
    RingHom.toAlgebra (overlapToTripleBase (R := R) (t := t) i j k).toRingHom
  letI : IsScalarTower R (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R (tripleRing (R := R) (t := t) i j k) r =
        (overlapToTripleBase (R := R) (t := t) i j k) (algebraMap R (overlapRing (R := R) (t := t) i j) r)
      exact ((overlapToTripleBase (R := R) (t := t) i j k).commutes r).symm
  let u : overlapFixed (R := R) (A := A) (G := G) (t := t) i j →ₐ[overlapRing (R := R) (t := t) i j]
      tripleRing (R := R) (t := t) i j k ⊗[overlapRing (R := R) (t := t) i j] overlapFixed (R := R) (A := A) (G := G) (t := t) i j :=
    Algebra.TensorProduct.includeRight
  exact (m1Triple (R := R) (A := A) (G := G) t i j k).toAlgHom.comp
    ((Algebra.TensorProduct.cancelBaseChange (R := R) (S := overlapRing (R := R) (t := t) i j)
      (T := tripleRing (R := R) (t := t) i j k) (A := tripleRing (R := R) (t := t) i j k)
      (B := FixedPoints.subalgebra R A G)).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id (R := overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k) (tripleRing (R := R) (t := t) i j k))
        (m1Overlap (R := R) (A := A) (G := G) t i j).symm.toAlgHom).comp u))


/-- Coefficient formula for the corrected overlap-to-triple map. -/
theorem overlapToTriple_coe (i j k : ι)
    (x : overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
    ((overlapToTriple (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (x : overlapRing (R := R) (t := t) i j ⊗[R] A) := by
  apply overlapFixed_induction
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp [overlapToTriple]
  | add y₁ y₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | tmul b a =>
      simpa [m1Overlap_coe_tmul] using overlapToTriple_pure (R := R) (A := A) (G := G) t i j k b a


/-- Pure-tensor case of the corrected overlap-to-triple coefficient. -/
theorem overlapToTriple_pure (i j k : ι)
    (b : overlapRing (R := R) (t := t) i j) (a : FixedPoints.subalgebra R A G) :
    ((overlapToTriple (R := R) (A := A) (G := G) t i j k
        (m1Overlap (R := R) (A := A) (G := G) t i j (b ⊗ₜ[R] a)) :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (b ⊗ₜ[R] (a : A)) := by
  simp [overlapToTriple, m1Overlap_coe_tmul, m1Triple, overlapToTripleBase,
    Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul]

/-- The M1 equivalence at the chart. -/
noncomputable def m1Chart (i : ι) :
    chartRing (R := R) (t := t) i ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[chartRing (R := R) (t := t) i]
      chartFixed (R := R) (A := A) (G := G) (t := t) i :=
  letI : Module.Flat R (chartRing (R := R) (t := t) i) :=
    IsLocalization.flat (chartRing (R := R) (t := t) i) (Submonoid.powers (t i))
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := chartRing (R := R) (t := t) i)

/-- The corrected chart-to-overlap fixed-point map. -/
noncomputable def chartToOverlapFixed (i j : ι) :
    chartFixed (R := R) (A := A) (G := G) (t := t) i →ₐ[R]
      overlapFixed (R := R) (A := A) (G := G) (t := t) i j := by
  letI : Algebra (chartRing (R := R) (t := t) i) (overlapRing (R := R) (t := t) i j) :=
    RingHom.toAlgebra (IsLocalization.Away.awayToAwayRight (t i) (t j))
  letI : IsScalarTower R (chartRing (R := R) (t := t) i) (overlapRing (R := R) (t := t) i j) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R (overlapRing (R := R) (t := t) i j) r =
        IsLocalization.Away.awayToAwayRight (t i) (t j) (algebraMap R (chartRing (R := R) (t := t) i) r)
      exact (IsLocalization.Away.awayToAwayRight_eq (t i) (t j) r).symm
  exact (m1Overlap (R := R) (A := A) (G := G) t i j).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id (R := chartRing (R := R) (t := t) i)
      (overlapRing (R := R) (t := t) i j) (overlapRing (R := R) (t := t) i j))
      (AlgHom.id R (FixedPoints.subalgebra R A G))).comp
      (m1Chart (R := R) (A := A) (G := G) t i).symm.toAlgHom)

/-- Chart-to-triple map through `(i,j)`. -/
noncomputable def chartToTripleIJ (i j k : ι) :
    chartFixed (R := R) (A := A) (G := G) (t := t) i →ₐ[R]
      tripleFixed (R := R) (A := A) (G := G) (t := t) i j k :=
  (overlapToTriple (R := R) (A := A) (G := G) t i j k).comp
    (chartToOverlapFixed (R := R) (A := A) (G := G) t i j)

/-- Chart-to-triple map through `(i,k)`. -/
noncomputable def chartToTripleIK (i j k : ι) :
    chartFixed (R := R) (A := A) (G := G) (t := t) i →ₐ[R]
      tripleFixed (R := R) (A := A) (G := G) (t := t) i j k :=
  (overlapToTriple (R := R) (A := A) (G := G) t i k j).comp
    (chartToOverlapFixed (R := R) (A := A) (G := G) t i k)

/-- The two chart-to-triple base maps agree. -/
theorem chartToTripleBase_eq (i j k : ι) :
    (overlapToTripleBase (R := R) (t := t) i j k).toRingHom.comp
        (IsLocalization.Away.awayToAwayRight (t i) (t j)) =
      (overlapToTripleBase (R := R) (t := t) i k j).toRingHom.comp
        (IsLocalization.Away.awayToAwayRight (t i) (t k)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (t i))
  intro r
  simp [overlapToTripleBase, IsLocalization.Away.awayToAwayRight_eq]

/-- Tensor-level equality of the two chart-to-triple maps. -/
theorem chartTensorIJ_eq_IK (i j k : ι)
    (x : chartRing (R := R) (t := t) i ⊗[R] FixedPoints.subalgebra R A G) :
    Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A)
        (Algebra.TensorProduct.map (IsLocalization.Away.awayToAwayRight (t i) (t j))
          (AlgHom.id R (FixedPoints.subalgebra R A G)) x) =
      Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i k j)
        (AlgHom.id R A)
        (Algebra.TensorProduct.map (IsLocalization.Away.awayToAwayRight (t i) (t k))
          (AlgHom.id R (FixedPoints.subalgebra R A G)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | tmul a b =>
      simp [chartToTripleBase_eq (R := R) (t := t) i j k,
        Algebra.TensorProduct.map_tmul]

/-- Corrected chart-map equality. -/
theorem chartToTripleIJ_eq_IK (i j k : ι) :
    chartToTripleIJ (R := R) (A := A) (G := G) t i j k =
      chartToTripleIK (R := R) (A := A) (G := G) t i j k := by
  apply AlgHom.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  rw [chartToTripleIJ, AlgHom.comp_apply, chartToTripleIK, AlgHom.comp_apply]
  exact chartTensorIJ_eq_IK (R := R) (A := A) (G := G) t i j k x

/-- Scheme-level equality induced by the corrected chart-map equality. -/
theorem chartToTriple_spec_eq (i j k : ι) :
    Spec.map (CommRingCat.ofHom
        (chartToTripleIJ (R := R) (A := A) (G := G) t i j k).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (chartToTripleIK (R := R) (A := A) (G := G) t i j k).toRingHom) :=
  congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (chartToTripleIJ_eq_IK (R := R) (A := A) (G := G) t i j k)

end ABCBridge.JKFinalSelfContained