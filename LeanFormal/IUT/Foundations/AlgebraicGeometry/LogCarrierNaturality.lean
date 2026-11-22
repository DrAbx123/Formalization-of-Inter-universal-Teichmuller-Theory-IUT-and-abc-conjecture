import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.Foundations.LocalFields.UnscaledUnitLogLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! Unscaled log naturality over the actual completion isomorphism. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.LogCarrierNaturality

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

local instance normalizedCompletionNormedAlgebraAtPrime
    (place : FinitePlaceAtPrime F p) :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

theorem isometry_ringEquiv_symm {K L : Type*} [NormedField K] [NormedField L]
    (e : K ≃+* L) (he : Isometry (e : K → L)) :
    Isometry (e.symm : L → K) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [← he.dist_eq (e.symm y) (e.symm z)]
  simp

variable (place : FinitePlaceAtPrime F p)

abbrev SourceCompletion : Type _ := CommonPrimeCompletion place
abbrev TargetCompletion : Type _ := NormalizedCompletion place.val

/-- The production completion isomorphism. -/
def completionIsometryEquiv : SourceCompletion place ≃+* TargetCompletion place :=
  commonPrimeCompletionRingEquiv place

theorem completionIsometryEquiv_isometry :
    Isometry (completionIsometryEquiv place : SourceCompletion place → TargetCompletion place) :=
  isometry_commonPrimeCompletionRingEquiv place

theorem completionIsometryEquiv_symm_isometry :
    Isometry ((completionIsometryEquiv place).symm : TargetCompletion place → SourceCompletion place) :=
  isometry_ringEquiv_symm _ (completionIsometryEquiv_isometry place)

/-- The unscaled unit-log image as a set. -/
def unscaledUnitLogImage (K : Type*) [NormedField K] [CharZero K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [NormedAlgebra ℚ_[p] K] : Set K :=
  Set.range (unitLog (K := K))

/-- Unscaled log naturality square over the actual completion isometry. -/
theorem unitLog_naturality (u : (Integers (SourceCompletion place))ˣ) :
    completionIsometryEquiv place (unitLog (K := SourceCompletion place) u) =
      unitLog (K := TargetCompletion place)
        (integralUnitMap (completionIsometryEquiv place).toRingHom
          (completionIsometryEquiv_isometry place) u) := by
  exact unitLog_map (p := p) (completionIsometryEquiv place).toRingHom
    (completionIsometryEquiv_isometry place) u

theorem map_mem_unscaledUnitLogImage {x : SourceCompletion place}
    (hx : x ∈ unscaledUnitLogImage (p := p) (K := SourceCompletion place)) :
    completionIsometryEquiv place x ∈ unscaledUnitLogImage (p := p) (K := TargetCompletion place) := by
  rcases hx with ⟨u, rfl⟩
  exact ⟨integralUnitMap (completionIsometryEquiv place).toRingHom
    (completionIsometryEquiv_isometry place) u, (unitLog_naturality place u).symm⟩

theorem map_symm_mem_unscaledUnitLogImage {y : TargetCompletion place}
    (hy : y ∈ unscaledUnitLogImage (p := p) (K := TargetCompletion place)) :
    (completionIsometryEquiv place).symm y ∈ unscaledUnitLogImage (p := p) (K := SourceCompletion place) := by
  rcases hy with ⟨v, rfl⟩
  refine ⟨integralUnitMap (completionIsometryEquiv place).symm.toRingHom
    (completionIsometryEquiv_symm_isometry place) v, ?_⟩
  exact (unitLog_map (p := p) (completionIsometryEquiv place).symm.toRingHom
    (completionIsometryEquiv_symm_isometry place) v).symm

theorem image_unscaledUnitLogImage :
    (completionIsometryEquiv place) '' (unscaledUnitLogImage (p := p) (K := SourceCompletion place)) =
      unscaledUnitLogImage (p := p) (K := TargetCompletion place) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact map_mem_unscaledUnitLogImage place hx
  · intro hy
    exact ⟨(completionIsometryEquiv place).symm y,
      map_symm_mem_unscaledUnitLogImage place hy,
      (completionIsometryEquiv place).apply_symm_apply y⟩

theorem map_mem_integralLogShell {x : SourceCompletion place}
    (hx : x ∈ integralLogShell (K := SourceCompletion place) (p := p)) :
    completionIsometryEquiv place x ∈ integralLogShell (K := TargetCompletion place) (p := p) :=
  LocalFieldLogarithm.map_mem_integralLogShell (p := p)
    (completionIsometryEquiv place).toRingHom
    (completionIsometryEquiv_isometry place) hx

theorem map_symm_mem_integralLogShell {y : TargetCompletion place}
    (hy : y ∈ integralLogShell (K := TargetCompletion place) (p := p)) :
    (completionIsometryEquiv place).symm y ∈ integralLogShell (K := SourceCompletion place) (p := p) :=
  LocalFieldLogarithm.map_mem_integralLogShell (p := p)
    (completionIsometryEquiv place).symm.toRingHom
    (completionIsometryEquiv_symm_isometry place) hy

theorem map_mem_unitLogLattice {x : SourceCompletion place}
    (hx : x ∈ unitLogLattice (K := SourceCompletion place) (p := p)) :
    completionIsometryEquiv place x ∈ unitLogLattice (K := TargetCompletion place) (p := p) := by
  rw [unitLogLattice, Submodule.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [unitLogLattice, Submodule.mem_map]
  refine ⟨completionIsometryEquiv place y, ?_, ?_⟩
  · exact map_mem_integralLogShell place hy
  · rw [unitLogScaleMul_apply, unitLogScaleMul_apply, map_mul, map_natCast]

theorem map_symm_mem_unitLogLattice {y : TargetCompletion place}
    (hy : y ∈ unitLogLattice (K := TargetCompletion place) (p := p)) :
    (completionIsometryEquiv place).symm y ∈ unitLogLattice (K := SourceCompletion place) (p := p) := by
  rw [unitLogLattice, Submodule.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [unitLogLattice, Submodule.mem_map]
  refine ⟨(completionIsometryEquiv place).symm z, ?_, ?_⟩
  · exact map_symm_mem_integralLogShell place hz
  · rw [unitLogScaleMul_apply, unitLogScaleMul_apply, map_mul, map_natCast]

/-- Additive comparison of the unscaled unit-log lattices. -/
noncomputable def unitLogLatticeAddEquiv :
    (unitLogLattice (K := SourceCompletion place) (p := p)) ≃+
      (unitLogLattice (K := TargetCompletion place) (p := p)) where
  toFun x := ⟨completionIsometryEquiv place x, map_mem_unitLogLattice place x.2⟩
  invFun y := ⟨(completionIsometryEquiv place).symm y,
    map_symm_mem_unitLogLattice place y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (completionIsometryEquiv place).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (completionIsometryEquiv place).apply_symm_apply y
  map_add' x y := by
    apply Subtype.ext
    exact (completionIsometryEquiv place).map_add x y

/-- Multiplicative comparison: the induced unit map is multiplicative and
intertwines the unscaled logarithm. -/
theorem unitLog_naturality_multiplicative (u v : (Integers (SourceCompletion place))ˣ) :
    completionIsometryEquiv place (unitLog (K := SourceCompletion place) (u * v)) =
      unitLog (K := TargetCompletion place)
        (integralUnitMap (completionIsometryEquiv place).toRingHom
          (completionIsometryEquiv_isometry place) (u * v)) :=
  unitLog_naturality place (u * v)

theorem integralUnitMap_mul (u v : (Integers (SourceCompletion place))ˣ) :
    integralUnitMap (completionIsometryEquiv place).toRingHom
        (completionIsometryEquiv_isometry place) (u * v) =
      integralUnitMap (completionIsometryEquiv place).toRingHom
        (completionIsometryEquiv_isometry place) u *
      integralUnitMap (completionIsometryEquiv place).toRingHom
        (completionIsometryEquiv_isometry place) v :=
  map_mul _ _ _

end LeanFormal.N8.LogCarrierNaturality
