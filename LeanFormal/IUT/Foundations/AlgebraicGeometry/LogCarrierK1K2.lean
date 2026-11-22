import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.Foundations.LocalFields.UnscaledUnitLogLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! K1/K2 naturality square over the actual completion isometry. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.LogCarrierK1K2

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

variable (place : FinitePlaceAtPrime F p)

abbrev SourceCompletion : Type _ := CommonPrimeCompletion place
abbrev TargetCompletion : Type _ := NormalizedCompletion place.val

/-- The production completion isomorphism. -/
def completionIsometryEquiv : SourceCompletion place ≃+* TargetCompletion place :=
  commonPrimeCompletionRingEquiv place

theorem completionIsometryEquiv_isometry :
    Isometry (completionIsometryEquiv place : SourceCompletion place → TargetCompletion place) :=
  isometry_commonPrimeCompletionRingEquiv place

/-- K1: the unit group maps into the unscaled unit-log lattice by `unitLog`. -/
def unitLogToLattice (K : Type*) [NormedField K] [CharZero K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    (u : (Integers K)ˣ) : unitLogLattice (K := K) (p := p) :=
  ⟨unitLog (K := K) u, (mem_unitLogLattice_iff (K := K) (p := p)).mpr ⟨u, rfl⟩⟩

theorem map_mem_unitLogLattice {x : SourceCompletion place}
    (hx : x ∈ unitLogLattice (K := SourceCompletion place) (p := p)) :
    completionIsometryEquiv place x ∈ unitLogLattice (K := TargetCompletion place) (p := p) := by
  rw [unitLogLattice, Submodule.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [unitLogLattice, Submodule.mem_map]
  refine ⟨completionIsometryEquiv place y, ?_, ?_⟩
  · exact LocalFieldLogarithm.map_mem_integralLogShell (p := p)
      (completionIsometryEquiv place).toRingHom
      (completionIsometryEquiv_isometry place) hy
  · rw [unitLogScaleMul_apply, unitLogScaleMul_apply, map_mul, map_natCast]

/-- The K2 comparison map on the unscaled unit-log lattices induced by the
actual completion isometry. -/
noncomputable def K2Map :
    (unitLogLattice (K := SourceCompletion place) (p := p)) →
      (unitLogLattice (K := TargetCompletion place) (p := p)) :=
  fun x => ⟨completionIsometryEquiv place (x : SourceCompletion place),
    map_mem_unitLogLattice place x.2⟩

theorem K2Map_add (x y : unitLogLattice (K := SourceCompletion place) (p := p)) :
    K2Map place (x + y) = K2Map place x + K2Map place y := by
  apply Subtype.ext
  exact (completionIsometryEquiv place).map_add (x : SourceCompletion place) (y : SourceCompletion place)

theorem K1K2_naturality (u : (Integers (SourceCompletion place))ˣ) :
    K2Map place (unitLogToLattice (K := SourceCompletion place) (p := p) u) =
      unitLogToLattice (K := TargetCompletion place) (p := p)
        (integralUnitMap (completionIsometryEquiv place).toRingHom
          (completionIsometryEquiv_isometry place) u) := by
  apply Subtype.ext
  exact unitLog_map (p := p) (completionIsometryEquiv place).toRingHom
    (completionIsometryEquiv_isometry place) u

theorem K1K2_naturality_mul (u v : (Integers (SourceCompletion place))ˣ) :
    K2Map place (unitLogToLattice (K := SourceCompletion place) (p := p) (u * v)) =
      unitLogToLattice (K := TargetCompletion place) (p := p)
        (integralUnitMap (completionIsometryEquiv place).toRingHom
          (completionIsometryEquiv_isometry place) (u * v)) :=
  K1K2_naturality place (u * v)

theorem integralUnitMap_mul (u v : (Integers (SourceCompletion place))ˣ) :
    integralUnitMap (completionIsometryEquiv place).toRingHom
        (completionIsometryEquiv_isometry place) (u * v) =
      integralUnitMap (completionIsometryEquiv place).toRingHom
        (completionIsometryEquiv_isometry place) u *
      integralUnitMap (completionIsometryEquiv place).toRingHom
        (completionIsometryEquiv_isometry place) v :=
  map_mul _ _ _

end LeanFormal.N8.LogCarrierK1K2
