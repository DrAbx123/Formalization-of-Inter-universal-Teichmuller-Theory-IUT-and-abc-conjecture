import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! Consumer interface: actual unscaled log image equivalence and the
unitLog_map square.  The image equivalence is built only from an isometric
ring equivalence (no raw-norm assumption); its underlying value formula is
val(e_L x) = e(val x). -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.LogUnscaledImageConsumer

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

theorem isometry_ringEquiv_symm {K L : Type*} [NormedField K] [NormedField L]
    (e : K ≃+* L) (he : Isometry (e : K → L)) :
    Isometry (e.symm : L → K) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [← he.dist_eq (e.symm y) (e.symm z)]
  simp

section Generic

variable {K L : Type*}
  [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] [ProperSpace K]
  [NormedField L] [IsUltrametricDist L] [CharZero L] [CompleteSpace L] [ProperSpace L]
  {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]

/-- The unscaled logarithm image as a set. -/
def unscaledLogImage (K : Type*) [NormedField K] [CharZero K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [NormedAlgebra ℚ_[p] K] : Set K :=
  Set.range (unitLog (K := K))

theorem unitLog_mem_unscaledLogImage (u : (Integers K)ˣ) :
    unitLog (K := K) u ∈ unscaledLogImage (p := p) (K := K) := by
  exact ⟨u, rfl⟩

/-- The unscaled log image equivalence induced by an isometric ring
equivalence.  Its underlying value formula is recorded below. -/
noncomputable def unscaledLogImageEquiv (e : K ≃+* L) (he : Isometry (e : K → L)) :
    (unscaledLogImage (p := p) (K := K)) ≃ (unscaledLogImage (p := p) (K := L)) where
  toFun x :=
    ⟨e (x : K), by
      obtain ⟨u, hu⟩ := x.2
      exact ⟨integralUnitMap e.toRingHom he u, by
        rw [← unitLog_map (p := p) e.toRingHom he u]
        rw [hu]
        rfl⟩⟩
  invFun y :=
    ⟨e.symm (y : L), by
      obtain ⟨v, hv⟩ := y.2
      exact ⟨integralUnitMap e.symm.toRingHom (isometry_ringEquiv_symm e he) v, by
        rw [← unitLog_map (p := p) e.symm.toRingHom (isometry_ringEquiv_symm e he) v]
        rw [hv]
        rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply (x : K)
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply (y : L)

/-- Underlying formula of the unscaled image equivalence. -/
theorem unscaledLogImageEquiv_val (e : K ≃+* L) (he : Isometry (e : K → L))
    (x : unscaledLogImage (p := p) (K := K)) :
    (unscaledLogImageEquiv (p := p) e he x : L) = e (x : K) := rfl

/-- The `unitLog_map` square, packaged as the definitional action of the
unscaled image equivalence on logarithms. -/
theorem unscaledLogImageEquiv_unitLog (e : K ≃+* L) (he : Isometry (e : K → L))
    (u : (Integers K)ˣ) :
    unscaledLogImageEquiv (p := p) e he
        ⟨unitLog (K := K) u, unitLog_mem_unscaledLogImage (p := p) u⟩ =
      ⟨unitLog (K := L) (integralUnitMap e.toRingHom he u),
        unitLog_mem_unscaledLogImage (p := p)
          (integralUnitMap e.toRingHom he u)⟩ := by
  apply Subtype.ext
  exact unitLog_map (p := p) e.toRingHom he u

theorem unscaledLogImageEquiv_unitLog_val (e : K ≃+* L) (he : Isometry (e : K → L))
    (u : (Integers K)ˣ) :
    (unscaledLogImageEquiv (p := p) e he
        ⟨unitLog (K := K) u, unitLog_mem_unscaledLogImage (p := p) u⟩ : L) =
      unitLog (K := L) (integralUnitMap e.toRingHom he u) :=
  Subtype.ext_iff.mp (unscaledLogImageEquiv_unitLog (p := p) e he u)

theorem integralUnitMap_mul (e : K ≃+* L) (he : Isometry (e : K → L))
    (u v : (Integers K)ˣ) :
    integralUnitMap e.toRingHom he (u * v) =
      integralUnitMap e.toRingHom he u * integralUnitMap e.toRingHom he v :=
  map_mul _ _ _

end Generic

section ActualCompletion

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

/-- The actual completion isometric ring equivalence. -/
def completionIsometryEquiv : SourceCompletion place ≃+* TargetCompletion place :=
  commonPrimeCompletionRingEquiv place

theorem completionIsometryEquiv_isometry :
    Isometry (completionIsometryEquiv place : SourceCompletion place → TargetCompletion place) :=
  isometry_commonPrimeCompletionRingEquiv place

/-- Consumer interface: the actual unscaled log image equivalence at the
completion. -/
noncomputable def actualUnscaledLogImageEquiv :
    (unscaledLogImage (p := p) (K := SourceCompletion place)) ≃
      (unscaledLogImage (p := p) (K := TargetCompletion place)) :=
  unscaledLogImageEquiv (p := p) (completionIsometryEquiv place)
    (completionIsometryEquiv_isometry place)

theorem actualUnscaledLogImageEquiv_val
    (x : unscaledLogImage (p := p) (K := SourceCompletion place)) :
    (actualUnscaledLogImageEquiv place x : TargetCompletion place) =
      completionIsometryEquiv place (x : SourceCompletion place) := rfl

theorem actualUnscaledLogImageEquiv_unitLog (u : (Integers (SourceCompletion place))ˣ) :
    actualUnscaledLogImageEquiv place
        ⟨unitLog (K := SourceCompletion place) u,
          unitLog_mem_unscaledLogImage (p := p) u⟩ =
      ⟨unitLog (K := TargetCompletion place)
          (integralUnitMap (completionIsometryEquiv place).toRingHom
            (completionIsometryEquiv_isometry place) u),
        unitLog_mem_unscaledLogImage (p := p)
          (integralUnitMap (completionIsometryEquiv place).toRingHom
            (completionIsometryEquiv_isometry place) u)⟩ :=
  unscaledLogImageEquiv_unitLog (p := p) (completionIsometryEquiv place)
    (completionIsometryEquiv_isometry place) u

end ActualCompletion

end LeanFormal.N8.LogUnscaledImageConsumer
