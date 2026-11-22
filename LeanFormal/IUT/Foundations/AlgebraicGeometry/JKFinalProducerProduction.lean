import Mathlib.RingTheory.Flat.Localization
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct

namespace ABCBridge.JKFinalProducerProduction
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



/-- Corrected `(i,k)` overlap-to-triple fixed-point map with common target. -/
noncomputable def overlapIKToTriple (i j k : ι) :
    overlapFixed (R := R) (A := A) (G := G) (t := t) i k →ₐ[R]
      tripleFixed (R := R) (A := A) (G := G) (t := t) i j k := by
  letI : Algebra (overlapRing (R := R) (t := t) i k) (tripleRing (R := R) (t := t) i j k) :=
    RingHom.toAlgebra (overlapIKToTripleBase (R := R) (t := t) i j k).toRingHom
  letI : IsScalarTower R (overlapRing (R := R) (t := t) i k) (tripleRing (R := R) (t := t) i j k) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R (tripleRing (R := R) (t := t) i j k) r =
        (overlapIKToTripleBase (R := R) (t := t) i j k) (algebraMap R (overlapRing (R := R) (t := t) i k) r)
      exact ((overlapIKToTripleBase (R := R) (t := t) i j k).commutes r).symm
  let u : overlapFixed (R := R) (A := A) (G := G) (t := t) i k →ₐ[overlapRing (R := R) (t := t) i k]
      tripleRing (R := R) (t := t) i j k ⊗[overlapRing (R := R) (t := t) i k] overlapFixed (R := R) (A := A) (G := G) (t := t) i k :=
    Algebra.TensorProduct.includeRight
  exact (m1Triple (R := R) (A := A) (G := G) t i j k).toAlgHom.comp
    ((Algebra.TensorProduct.cancelBaseChange (R := R) (S := overlapRing (R := R) (t := t) i k)
      (T := tripleRing (R := R) (t := t) i j k) (A := tripleRing (R := R) (t := t) i j k)
      (B := FixedPoints.subalgebra R A G)).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id (R := overlapRing (R := R) (t := t) i k)
        (tripleRing (R := R) (t := t) i j k) (tripleRing (R := R) (t := t) i j k))
        (m1Overlap (R := R) (A := A) (G := G) t i k).symm.toAlgHom).comp u))

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

/-- Explicit `AlgHom` wrapper for the away localization map. -/
noncomputable def awayToAwayAlgHom (i j : ι) :
    chartRing (R := R) (t := t) i →ₐ[R] overlapRing (R := R) (t := t) i j :=
  { toRingHom := IsLocalization.Away.awayToAwayRight (t i) (t j)
    commutes' := fun r => by
      change IsLocalization.Away.awayToAwayRight (t i) (t j)
        (algebraMap R (chartRing (R := R) (t := t) i) r) =
        algebraMap R (overlapRing (R := R) (t := t) i j) r
      exact IsLocalization.Away.awayToAwayRight_eq (t i) (t j) r }

/-- The corrected chart-to-overlap fixed-point map. -/
noncomputable def chartToOverlapFixed (i j : ι) :
    chartFixed (R := R) (A := A) (G := G) (t := t) i →ₐ[R]
      overlapFixed (R := R) (A := A) (G := G) (t := t) i j := by
  letI : Algebra (chartRing (R := R) (t := t) i) (overlapRing (R := R) (t := t) i j) :=
    RingHom.toAlgebra ((awayToAwayAlgHom (R := R) (t := t) i j).toRingHom)
  letI : IsScalarTower R (chartRing (R := R) (t := t) i) (overlapRing (R := R) (t := t) i j) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R (overlapRing (R := R) (t := t) i j) r =
        (awayToAwayAlgHom (R := R) (t := t) i j).toRingHom (algebraMap R (chartRing (R := R) (t := t) i) r)
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
  (overlapIKToTriple (R := R) (A := A) (G := G) t i j k).comp
    (chartToOverlapFixed (R := R) (A := A) (G := G) t i k)

/-- The two chart-to-triple base maps agree, with common target `tripleRing i j k`. -/
theorem chartToTripleBase_eq (i j k : ι) :
    (overlapToTripleBase (R := R) (t := t) i j k).toRingHom.comp
        ((awayToAwayAlgHom (R := R) (t := t) i j).toRingHom) =
      (overlapIKToTripleBase (R := R) (t := t) i j k).toRingHom.comp
        ((awayToAwayAlgHom (R := R) (t := t) i k).toRingHom) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (t i))
  intro r
  rw [RingHom.comp_apply, RingHom.comp_apply,
    IsLocalization.Away.awayToAwayRight_eq (t i) (t j) r,
    IsLocalization.Away.awayToAwayRight_eq (t i) (t k) r,
    (overlapToTripleBase (R := R) (t := t) i j k).commutes r,
    (overlapIKToTripleBase (R := R) (t := t) i j k).commutes r]

/-- Tensor-level equality of the two chart-to-triple maps. -/
theorem chartTensorIJ_eq_IK (i j k : ι)
    (x : chartRing (R := R) (t := t) i ⊗[R] FixedPoints.subalgebra R A G) :
    Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A)
        (Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i j)
          (AlgHom.id R (FixedPoints.subalgebra R A G)) x) =
      Algebra.TensorProduct.map (overlapIKToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A)
        (Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i k)
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


/-- Pure-tensor coefficient for the `(i,k)` common-target map. -/
theorem overlapIKToTriple_pure (i j k : ι)
    (b : overlapRing (R := R) (t := t) i k) (a : FixedPoints.subalgebra R A G) :
    ((overlapIKToTriple (R := R) (A := A) (G := G) t i j k
        (m1Overlap (R := R) (A := A) (G := G) t i k (b ⊗ₜ[R] a)) :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapIKToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (b ⊗ₜ[R] (a : A)) := by
  apply Subtype.ext
  simp only [overlapIKToTriple, AlgHom.comp_apply, m1Overlap_coe_tmul,
    m1Triple, overlapIKToTripleBase, Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_comp, Function.comp_apply]

/-- All-fixed-point coefficient for the `(i,k)` common-target map. -/
theorem overlapIKToTriple_coe (i j k : ι)
    (x : overlapFixed (R := R) (A := A) (G := G) (t := t) i k) :
    ((overlapIKToTriple (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapIKToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (x : overlapRing (R := R) (t := t) i k ⊗[R] A) := by
  apply overlapFixed_induction (i := i) (j := k)
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add]
  | tmul b a =>
      exact overlapIKToTriple_pure (R := R) (A := A) (G := G) t i j k b a

/-- Pure-tensor coefficient for the chart M1 equivalence. -/
theorem m1Chart_coe_tmul (i : ι)
    (a : chartRing (R := R) (t := t) i) (b : FixedPoints.subalgebra R A G) :
    ((m1Chart (R := R) (A := A) (G := G) t i (a ⊗ₜ[R] b) :
        chartFixed (R := R) (A := A) (G := G) (t := t) i) :
        chartRing (R := R) (t := t) i ⊗[R] A) =
      a ⊗ₜ[R] (b : A) := by
  simp only [m1Chart, M1Final.tensorFixedPointsAlgEquiv,
    AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]

/-- Round-trip identity for `m1Chart`. -/
theorem m1Chart_apply_symm (i : ι)
    (x : chartFixed (R := R) (A := A) (G := G) (t := t) i) :
    m1Chart (R := R) (A := A) (G := G) t i ((m1Chart (R := R) (A := A) (G := G) t i).symm x) = x :=
  (m1Chart (R := R) (A := A) (G := G) t i).apply_symm_apply x

/-- M1 induction principle for the chart fixed points. -/
theorem chartFixed_induction (i : ι)
    {P : chartFixed (R := R) (A := A) (G := G) (t := t) i → Prop}
    (h : ∀ y : chartRing (R := R) (t := t) i ⊗[R] FixedPoints.subalgebra R A G,
      P (m1Chart (R := R) (A := A) (G := G) t i y)) :
    ∀ x, P x := by
  intro x
  rw [show x = m1Chart (R := R) (A := A) (G := G) t i
      ((m1Chart (R := R) (A := A) (G := G) t i).symm x) from
    ((m1Chart (R := R) (A := A) (G := G) t i).apply_symm_apply x).symm]
  exact h ((m1Chart (R := R) (A := A) (G := G) t i).symm x)

/-- Coefficient formula for the chart-to-overlap fixed map. -/
theorem chartToOverlapFixed_coe (i j : ι)
    (x : chartFixed (R := R) (A := A) (G := G) (t := t) i) :
    ((chartToOverlapFixed (R := R) (A := A) (G := G) t i j x :
        overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
        overlapRing (R := R) (t := t) i j ⊗[R] A) =
      Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i j)
        (AlgHom.id R A) (x : chartRing (R := R) (t := t) i ⊗[R] A) := by
  apply chartFixed_induction
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add]
  | tmul a b =>
      simp only [chartToOverlapFixed, AlgHom.comp_apply, m1Chart_coe_tmul,
        m1Overlap_coe_tmul, Algebra.TensorProduct.map_tmul]

/-- Explicit tensor-map composition for the `(i,k)` chart coefficient. -/
theorem tensorMap_comp_IK (i j k : ι)
    (x : chartRing (R := R) (t := t) i ⊗[R] FixedPoints.subalgebra R A G) :
    Algebra.TensorProduct.map (overlapIKToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A)
        (Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i k)
          (AlgHom.id R A) x) =
      Algebra.TensorProduct.map
        ((overlapIKToTripleBase (R := R) (t := t) i j k).toRingHom.comp
          ((awayToAwayAlgHom (R := R) (t := t) i k).toRingHom))
        (AlgHom.id R A) x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | tmul a b => simp only [Algebra.TensorProduct.map_tmul, RingHom.comp_apply]

/-- Explicit tensor-map composition for the `(i,j)` chart coefficient. -/
theorem tensorMap_comp_IJ (i j k : ι)
    (x : chartRing (R := R) (t := t) i ⊗[R] FixedPoints.subalgebra R A G) :
    Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A)
        (Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i j)
          (AlgHom.id R A) x) =
      Algebra.TensorProduct.map
        ((overlapToTripleBase (R := R) (t := t) i j k).toRingHom.comp
          ((awayToAwayAlgHom (R := R) (t := t) i j).toRingHom))
        (AlgHom.id R A) x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | tmul a b => simp only [Algebra.TensorProduct.map_tmul, RingHom.comp_apply]

/-- Coefficient formula for `chartToTripleIK`. -/
theorem chartToTripleIK_coe (i j k : ι)
    (x : chartFixed (R := R) (A := A) (G := G) (t := t) i) :
    ((chartToTripleIK (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map
        ((overlapIKToTripleBase (R := R) (t := t) i j k).toRingHom.comp
          ((awayToAwayAlgHom (R := R) (t := t) i k).toRingHom))
        (AlgHom.id R A) (x : chartRing (R := R) (t := t) i ⊗[R] A) := by
  rw [chartToTripleIK, AlgHom.comp_apply, chartToOverlapFixed_coe, overlapIKToTriple_coe]
  exact tensorMap_comp_IK (R := R) (A := A) (G := G) t i j k x


/-- Coefficient formula for `chartToTripleIJ`. -/
theorem chartToTripleIJ_coe (i j k : ι)
    (x : chartFixed (R := R) (A := A) (G := G) (t := t) i) :
    ((chartToTripleIJ (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map
        ((overlapToTripleBase (R := R) (t := t) i j k).toRingHom.comp
          ((awayToAwayAlgHom (R := R) (t := t) i j).toRingHom))
        (AlgHom.id R A) (x : chartRing (R := R) (t := t) i ⊗[R] A) := by
  rw [chartToTripleIJ, AlgHom.comp_apply, chartToOverlapFixed_coe,
    overlapToTriple_coe]
  exact tensorMap_comp_IJ (R := R) (A := A) (G := G) t i j k x

/-- Corrected chart-map equality from the two coefficient formulas and the
common-target base comparison. -/
theorem chartToTripleIJ_eq_IK_final (i j k : ι) :
    chartToTripleIJ (R := R) (A := A) (G := G) t i j k =
      chartToTripleIK (R := R) (A := A) (G := G) t i j k := by
  apply AlgHom.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  rw [chartToTripleIJ_coe, chartToTripleIK_coe]
  exact congrArg (fun f => Algebra.TensorProduct.map f (AlgHom.id R A)
    (x : chartRing (R := R) (t := t) i ⊗[R] A)) (chartToTripleBase_eq (R := R) (t := t) i j k)

/-- Scheme-level JK square from the coefficient-level chart equality. -/
theorem chartToTriple_spec_eq_final (i j k : ι) :
    Spec.map (CommRingCat.ofHom
        (chartToTripleIJ (R := R) (A := A) (G := G) t i j k).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (chartToTripleIK (R := R) (A := A) (G := G) t i j k).toRingHom) :=
  congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (chartToTripleIJ_eq_IK_final (R := R) (A := A) (G := G) t i j k)


/-- **JK final consumer.**  The corrected chart-to-triple maps agree, and the
induced scheme-level square is the JK compatibility square.  This is the
production-facing form of the coefficient proof above. -/
theorem jkSquare (i j k : ι) :
    Spec.map (CommRingCat.ofHom
        (chartToTripleIJ (R := R) (A := A) (G := G) t i j k).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (chartToTripleIK (R := R) (A := A) (G := G) t i j k).toRingHom) :=
  chartToTriple_spec_eq_final (R := R) (A := A) (G := G) t i j k

end ABCBridge.JKFinalProducerProduction