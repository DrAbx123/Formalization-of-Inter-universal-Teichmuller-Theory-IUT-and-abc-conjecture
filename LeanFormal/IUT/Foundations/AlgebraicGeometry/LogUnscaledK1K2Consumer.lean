import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogUnscaledSourceConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogCarrierK1K2

/-! Combined unscaled/K1K2 consumer at an arbitrary finite-place actual completion. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.LogUnscaledK1K2Consumer

open LeanFormal.N8.LogCarrierK1K2
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
open scoped Pointwise

variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

local instance normalizedCompletionNormedAlgebraAtPrime
    (place : FinitePlaceAtPrime F p) :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

variable (place : FinitePlaceAtPrime F p)

/-- Forall-unit K1/K2 square at the actual completion: the K2 comparison map
on the unscaled unit-log lattice sends the logarithm of a unit to the
logarithm of the transported integral unit. -/
theorem actual_K2Map_unitLog_forall :
    ∀ u : (Integers (SourceCompletion place))ˣ,
      (K2Map place (unitLogToLattice (K := SourceCompletion place) (p := p) u) :
          TargetCompletion place) =
        unitLog (K := TargetCompletion place)
          (integralUnitMap (completionIsometryEquiv place).toRingHom
            (completionIsometryEquiv_isometry place) u) := by
  intro u
  simpa [unitLogToLattice] using
    (Subtype.ext_iff.mp (K1K2_naturality (p := p) place u))

/-- The source-consumer unscaled image equivalence and the K1/K2 comparison
map agree on every unit logarithm. -/
theorem actual_imageEquiv_agrees_K2Map (u : (Integers (SourceCompletion place))ˣ) :
    (LeanFormal.N8.LogUnscaledImageConsumer.actualUnscaledLogImageEquiv place
        ⟨unitLog (K := SourceCompletion place) u,
          LeanFormal.N8.LogUnscaledImageConsumer.unitLog_mem_unscaledLogImage
            (p := p) u⟩ : TargetCompletion place) =
      (K2Map place (unitLogToLattice (K := SourceCompletion place) (p := p) u) :
        TargetCompletion place) := by
  rw [LeanFormal.N8.LogUnscaledSourceConsumer.actualUnscaledLogImageEquiv_formula]
  rfl

/-- Additivity of the K2 comparison map at the arbitrary actual completion. -/
theorem actual_K2Map_add
    (x y : unitLogLattice (K := SourceCompletion place) (p := p)) :
    K2Map place (x + y) = K2Map place x + K2Map place y :=
  K2Map_add (p := p) place x y

/-- Exact scale: the paper's log-shell scale is p for odd p and p^2 for p=2. -/
theorem actual_logShellScale_eq :
    logShellScale p = if p = 2 then p ^ 2 else p := rfl

/-- Exact p/scale identity: the unscaled unit-log lattice is the log-shell
scale times the scaled shell lattice (source side, exact p). -/
theorem actual_unitLogLattice_scale_source :
    (unitLogLattice (K := SourceCompletion place) (p := p) :
        Set (SourceCompletion place)) =
      (logShellScale p : SourceCompletion place) •
        (integralLogShellLattice (K := SourceCompletion place) (p := p) :
          Set (SourceCompletion place)) :=
  coe_unitLogLattice_eq_scale_smul (K := SourceCompletion place) (p := p)

/-- Exact p/scale identity on the target side. -/
theorem actual_unitLogLattice_scale_target :
    (unitLogLattice (K := TargetCompletion place) (p := p) :
        Set (TargetCompletion place)) =
      (logShellScale p : TargetCompletion place) •
        (integralLogShellLattice (K := TargetCompletion place) (p := p) :
          Set (TargetCompletion place)) :=
  coe_unitLogLattice_eq_scale_smul (K := TargetCompletion place) (p := p)

/-- The unscaled unit-log lattice is exactly the unitLog image (source side),
so the K1/K2 lattice square and the unscaled image consumer live on the same
carrier at exact p. -/
theorem actual_unitLogLattice_range_source :
    (unitLogLattice (K := SourceCompletion place) (p := p) :
        Set (SourceCompletion place)) =
      Set.range (unitLog (K := SourceCompletion place)) :=
  coe_unitLogLattice_eq_range (K := SourceCompletion place) (p := p)

theorem actual_unitLogLattice_range_target :
    (unitLogLattice (K := TargetCompletion place) (p := p) :
        Set (TargetCompletion place)) =
      Set.range (unitLog (K := TargetCompletion place)) :=
  coe_unitLogLattice_eq_range (K := TargetCompletion place) (p := p)

end LeanFormal.N8.LogUnscaledK1K2Consumer
