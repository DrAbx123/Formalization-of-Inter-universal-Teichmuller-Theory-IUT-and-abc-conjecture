import tmp.sheaf.n8.closure.EtaSourceActionShellPreservation

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Norm-one unit shell preservation attempt

Proves the actual norm isometry of the unit action.  Norm preservation alone does
not imply set preservation of preLogShell/logShell; no production theorem
supplies the latter.  Identity action preservation is actual.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaRouteInterface
open LeanFormal.IUT.N8Closure.EtaSourceActionActual
open LeanFormal.IUT.N8Closure.EtaSourceActionShellPreservation
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaNormOneUnitShellPreservationActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance nativeShellNormedField : NormedField (NativeShell X).K :=
  inferInstanceAs (NormedField (CommonPrimeCompletion
    (K := X.S.arithmetic.Fmod) (badPlaceAtPrime X)))

/-- Norm-one unit action is a norm isometry of K. -/
theorem normOne_unit_preserves_norm
    (u : (NativeShell X).Kˣ) (hu : ‖(u : (NativeShell X).K)‖ = 1)
    (x : (NativeShell X).K) :
    ‖(u : (NativeShell X).K) * x‖ = ‖x‖ := by
  rw [norm_mul, hu, one_mul]

/-- Actual preservation for the identity unit. -/
theorem identity_unit_preserves_shells :
    nativeMulLinearEquiv (X := X) 1 '' Rval X = Rval X ∧
      nativeMulLinearEquiv (X := X) 1 '' Rss X = Rss X :=
  ⟨identity_preserves_preLogShell (X := X),
   identity_preserves_logShell (X := X)⟩

/-- Exact missing stability statement. -/
def NormOneShellStability : Prop :=
  NormOneUnitShellPreservation (X := X)

/-- The identity unit is the actual preservation witness available here. -/
theorem identity_is_actual_preservation_witness :
    nativeMulLinearEquiv (X := X) 1 '' Rval X = Rval X :=
  identity_preserves_preLogShell (X := X)

end LeanFormal.IUT.N8Closure.EtaNormOneUnitShellPreservationActual

end