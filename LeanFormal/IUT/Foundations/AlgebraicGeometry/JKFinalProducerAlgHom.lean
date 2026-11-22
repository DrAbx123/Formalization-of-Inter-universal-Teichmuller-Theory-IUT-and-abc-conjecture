import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Spec
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.JKOverlapPureTensorLemma

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry

namespace ABCBridge.JKFinalProducerAlgHom
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
  exact ((m1Triple (R := R) (A := A) (G := G) t i j k).toAlgHom.restrictScalars R).comp
    (((Algebra.TensorProduct.cancelBaseChange (R := R) (S := overlapRing (R := R) (t := t) i j)
      (T := tripleRing (R := R) (t := t) i j k) (A := tripleRing (R := R) (t := t) i j k)
      (B := FixedPoints.subalgebra R A G)).toAlgHom.restrictScalars R).comp
      (((Algebra.TensorProduct.map (AlgHom.id (R := overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k))
        (m1Overlap (R := R) (A := A) (G := G) t i j).symm.toAlgHom).restrictScalars R).comp (u.restrictScalars R)))



/-- Common-target `(i,k)` base map into `tripleRing i j k`, using `awayLift`. -/
noncomputable def overlapIKToTripleBase (i j k : ι) :
    overlapRing (R := R) (t := t) i k →ₐ[R] tripleRing (R := R) (t := t) i j k :=
  { toRingHom := Localization.awayLift
      (algebraMap R (tripleRing (R := R) (t := t) i j k)) (t i * t k)
      (by
        have hprod : IsUnit (algebraMap R (tripleRing (R := R) (t := t) i j k)
            (t i * t j * t k)) :=
          IsLocalization.Away.algebraMap_isUnit (t i * t j * t k)
        exact isUnit_of_dvd_unit
          ⟨algebraMap R (tripleRing (R := R) (t := t) i j k) (t j), by
            rw [← map_mul]
            congr 1
            ring⟩ hprod)
    commutes' := fun r => by
      change Localization.awayLift (algebraMap R (tripleRing (R := R) (t := t) i j k))
        (t i * t k) _ (algebraMap R (overlapRing (R := R) (t := t) i k) r) =
        algebraMap R (tripleRing (R := R) (t := t) i j k) r
      exact IsLocalization.Away.lift_eq _ _ r }

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
  exact ((m1Triple (R := R) (A := A) (G := G) t i j k).toAlgHom.restrictScalars R).comp
    (((Algebra.TensorProduct.cancelBaseChange (R := R) (S := overlapRing (R := R) (t := t) i k)
      (T := tripleRing (R := R) (t := t) i j k) (A := tripleRing (R := R) (t := t) i j k)
      (B := FixedPoints.subalgebra R A G)).toAlgHom.restrictScalars R).comp
      (((Algebra.TensorProduct.map (AlgHom.id (R := overlapRing (R := R) (t := t) i k)
        (tripleRing (R := R) (t := t) i j k))
        (m1Overlap (R := R) (A := A) (G := G) t i k).symm.toAlgHom).restrictScalars R).comp (u.restrictScalars R)))

/-- The `map id m1Overlap.symm` on `includeRight` is `includeRight` of the inverse. -/
theorem map_id_symm_includeRight (i j : ι)
    [Algebra (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k)]
    [IsScalarTower R (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k)]
    (y : overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
    (Algebra.TensorProduct.map (AlgHom.id (R := overlapRing (R := R) (t := t) i j)
        (tripleRing (R := R) (t := t) i j k))
      (m1Overlap (R := R) (A := A) (G := G) t i j).symm.toAlgHom)
      (Algebra.TensorProduct.includeRight y) =
    Algebra.TensorProduct.includeRight ((m1Overlap (R := R) (A := A) (G := G) t i j).symm y) := by
  rw [← AlgHom.comp_apply, Algebra.TensorProduct.map_comp_includeRight]
  rfl

/-- Pure-tensor coefficient for `m1Triple`. -/
theorem m1Triple_coe_tmul (i j k : ι)
    (a : tripleRing (R := R) (t := t) i j k) (b : FixedPoints.subalgebra R A G) :
    ((m1Triple (R := R) (A := A) (G := G) t i j k (a ⊗ₜ[R] b) :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      a ⊗ₜ[R] (b : A) := by
  simp [m1Triple, M1Final.tensorFixedPointsAlgEquiv,
    AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]

/-- Pure-tensor case of the corrected overlap-to-triple coefficient. -/
theorem overlapToTriple_pure (i j k : ι)
    (b : overlapRing (R := R) (t := t) i j) (a : FixedPoints.subalgebra R A G) :
    ((overlapToTriple (R := R) (A := A) (G := G) t i j k
        (m1Overlap (R := R) (A := A) (G := G) t i j (b ⊗ₜ[R] a)) :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (b ⊗ₜ[R] (a : A)) := by
  unfold overlapToTriple
  simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply]
  letI : Algebra (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k) :=
    RingHom.toAlgebra (overlapToTripleBase (R := R) (t := t) i j k).toRingHom
  letI : IsScalarTower R (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R (tripleRing (R := R) (t := t) i j k) r =
        (overlapToTripleBase (R := R) (t := t) i j k)
          (algebraMap R (overlapRing (R := R) (t := t) i j) r)
      exact ((overlapToTripleBase (R := R) (t := t) i j k).commutes r).symm
  rw [map_id_symm_includeRight, AlgEquiv.symm_apply_apply]
  rw [ABCBridge.JKOverlapPureTensorLemma.cancelBaseChange_includeRight_tmul
    (R := R) (A := A) (t := t) i j k b (a : A)]
  rw [m1Triple_coe_tmul]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

/-- Coefficient formula for the corrected overlap-to-triple map. -/
theorem overlapToTriple_coe (i j k : ι)
    (x : overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
    ((overlapToTriple (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (x : overlapRing (R := R) (t := t) i j ⊗[R] A) := by
  refine overlapFixed_induction (i := i) (j := j)
    (P := fun x => ((overlapToTriple (R := R) (A := A) (G := G) t i j k x :
      tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
      tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (x : overlapRing (R := R) (t := t) i j ⊗[R] A)) ?_
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add]
  | tmul b a =>
      simpa only [m1Overlap_coe_tmul, map_tmul] using overlapToTriple_pure (R := R) (A := A) (G := G) t i j k b a


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
  exact ((m1Overlap (R := R) (A := A) (G := G) t i j).toAlgHom.restrictScalars R).comp
    (((Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i j)
      (AlgHom.id R (FixedPoints.subalgebra R A G))).restrictScalars R).comp
      ((m1Chart (R := R) (A := A) (G := G) t i).symm.toAlgHom.restrictScalars R))

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
  ext r
  simp only [RingHom.comp_apply, AlgHom.comp_apply]
  rw [IsLocalization.Away.awayToAwayRight_eq (t i) (t j) r,
    IsLocalization.Away.awayToAwayRight_eq (t i) (t k) r,
    (overlapToTripleBase (R := R) (t := t) i j k).commutes r,
    (overlapIKToTripleBase (R := R) (t := t) i j k).commutes r]

/-- The same common-target equality as an `AlgHom` composition. -/
theorem chartToTripleBaseAlgHom_eq (i j k : ι) :
    (overlapToTripleBase (R := R) (t := t) i j k).comp
        (awayToAwayAlgHom (R := R) (t := t) i j) =
      (overlapIKToTripleBase (R := R) (t := t) i j k).comp
        (awayToAwayAlgHom (R := R) (t := t) i k) := by
  apply AlgHom.ext
  intro x
  have h := congrFun (congrArg (fun f : chartRing (R := R) (t := t) i →+* tripleRing (R := R) (t := t) i j k =>
      (f : chartRing (R := R) (t := t) i → tripleRing (R := R) (t := t) i j k))
    (chartToTripleBase_eq (R := R) (t := t) i j k)) x
  simpa [AlgHom.comp_apply, awayToAwayAlgHom] using h

/-- Pure-tensor coefficient for the `(i,k)` common-target map. -/
theorem overlapIKToTriple_pure (i j k : ι)
    (b : overlapRing (R := R) (t := t) i k) (a : FixedPoints.subalgebra R A G) :
    ((overlapIKToTriple (R := R) (A := A) (G := G) t i j k
        (m1Overlap (R := R) (A := A) (G := G) t i k (b ⊗ₜ[R] a)) :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapIKToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (b ⊗ₜ[R] (a : A)) := by
  unfold overlapIKToTriple
  simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply]
  letI : Algebra (overlapRing (R := R) (t := t) i k) (tripleRing (R := R) (t := t) i j k) :=
    RingHom.toAlgebra (overlapIKToTripleBase (R := R) (t := t) i j k).toRingHom
  letI : IsScalarTower R (overlapRing (R := R) (t := t) i k) (tripleRing (R := R) (t := t) i j k) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R (tripleRing (R := R) (t := t) i j k) r =
        (overlapIKToTripleBase (R := R) (t := t) i j k)
          (algebraMap R (overlapRing (R := R) (t := t) i k) r)
      exact ((overlapIKToTripleBase (R := R) (t := t) i j k).commutes r).symm
  rw [map_id_symm_includeRight, AlgEquiv.symm_apply_apply]
  rw [ABCBridge.JKOverlapPureTensorLemma.cancelBaseChange_includeRight_tmul
    (R := R) (A := A) (t := t) i k j b (a : A)]
  rw [m1Triple_coe_tmul]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

/-- All-fixed-point coefficient for the `(i,k)` common-target map. -/
theorem overlapIKToTriple_coe (i j k : ι)
    (x : overlapFixed (R := R) (A := A) (G := G) (t := t) i k) :
    ((overlapIKToTriple (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapIKToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (x : overlapRing (R := R) (t := t) i k ⊗[R] A) := by
  refine overlapFixed_induction (i := i) (j := k)
    (P := fun x => ((overlapIKToTriple (R := R) (A := A) (G := G) t i j k x :
      tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
      tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map (overlapIKToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A) (x : overlapRing (R := R) (t := t) i k ⊗[R] A)) ?_
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
        (FixedPoints.subalgebra R A G).val ((m1Chart (R := R) (A := A) (G := G) t i).symm x) := by
  refine chartFixed_induction (i := i)
    (P := fun x => ((chartToOverlapFixed (R := R) (A := A) (G := G) t i j x :
      overlapFixed (R := R) (A := A) (G := G) (t := t) i j) :
      overlapRing (R := R) (t := t) i j ⊗[R] A) =
      Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i j)
        (FixedPoints.subalgebra R A G).val
        ((m1Chart (R := R) (A := A) (G := G) t i).symm x)) ?_
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
          (FixedPoints.subalgebra R A G).val x) =
      Algebra.TensorProduct.map
        ((overlapIKToTripleBase (R := R) (t := t) i j k).comp
          (awayToAwayAlgHom (R := R) (t := t) i k))
        (FixedPoints.subalgebra R A G).val x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | tmul a b => simp only [Algebra.TensorProduct.map_tmul, AlgHom.comp_apply]

/-- Explicit tensor-map composition for the `(i,j)` chart coefficient. -/
theorem tensorMap_comp_IJ (i j k : ι)
    (x : chartRing (R := R) (t := t) i ⊗[R] FixedPoints.subalgebra R A G) :
    Algebra.TensorProduct.map (overlapToTripleBase (R := R) (t := t) i j k)
        (AlgHom.id R A)
        (Algebra.TensorProduct.map (awayToAwayAlgHom (R := R) (t := t) i j)
          (FixedPoints.subalgebra R A G).val x) =
      Algebra.TensorProduct.map
        ((overlapToTripleBase (R := R) (t := t) i j k).comp
          (awayToAwayAlgHom (R := R) (t := t) i j))
        (FixedPoints.subalgebra R A G).val x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | tmul a b => simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]

/-- Coefficient formula for `chartToTripleIK`. -/
theorem chartToTripleIK_coe (i j k : ι)
    (x : chartFixed (R := R) (A := A) (G := G) (t := t) i) :
    ((chartToTripleIK (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map
        ((overlapIKToTripleBase (R := R) (t := t) i j k).comp
          (awayToAwayAlgHom (R := R) (t := t) i k))
        (FixedPoints.subalgebra R A G).val ((m1Chart (R := R) (A := A) (G := G) t i).symm x) := by
  rw [chartToTripleIK, AlgHom.comp_apply, chartToOverlapFixed_coe, overlapIKToTriple_coe]
  exact tensorMap_comp_IK (R := R) (A := A) (G := G) t i j k x


/-- Coefficient formula for `chartToTripleIJ`. -/
theorem chartToTripleIJ_coe (i j k : ι)
    (x : chartFixed (R := R) (A := A) (G := G) (t := t) i) :
    ((chartToTripleIJ (R := R) (A := A) (G := G) t i j k x :
        tripleFixed (R := R) (A := A) (G := G) (t := t) i j k) :
        tripleRing (R := R) (t := t) i j k ⊗[R] A) =
      Algebra.TensorProduct.map
        ((overlapToTripleBase (R := R) (t := t) i j k).comp
          (awayToAwayAlgHom (R := R) (t := t) i j))
        (FixedPoints.subalgebra R A G).val ((m1Chart (R := R) (A := A) (G := G) t i).symm x) := by
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
    ((m1Chart (R := R) (A := A) (G := G) t i).symm ⟨x, hx⟩)) (chartToTripleBaseAlgHom_eq (R := R) (t := t) i j k)

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

end ABCBridge.JKFinalProducerAlgHom