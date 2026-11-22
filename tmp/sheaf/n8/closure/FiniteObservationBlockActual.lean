import tmp.sheaf.n8.closure.FiniteObservationHullProofs3
import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingActual

/-!
# FiniteObservationBlockActual

Attempt to instantiate the finite-observation certificate on an actual block.
Actual: `Kf`, the completion integer ring `Integers Kf`, and the `ℤ_[p]`-span
lattice `L`.  The actual source action `S` and finite-level `K_N` are not
constructed in the tree; the exact gap is recorded below.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.FiniteObservationBlockActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.N8Closure.FiniteObservationHullProofs
open LeanFormal.IUT.N8Closure.FiniteObservationHullProofs2
open LeanFormal.IUT.N8Closure.FiniteObservationHullProofs3
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev Zp : Type := ℤ_[nativePrime X]

local instance : Module (Zp X) (Kf X) :=
  Module.compHom (Kf X) (algebraMap (Zp X) (ℚ_[nativePrime X]))

/-- Actual `ℤ_[p]`-span of the completion integer ring in `Kf`. -/
def L : Submodule (Zp X) (Kf X) :=
  Submodule.span (Zp X) (Integers (Kf X) : Set (Kf X))

/-- Actual trivial inner/outer certificate on the lattice `L`. -/
theorem block_certificate_trivial :
    InnerOuterHullCertificate (V := Kf X)
      (⊤ : Subring (Zp X)) (L X) (L X) (L X) :=
  ⟨le_rfl, le_rfl, rfl⟩

theorem block_hull_eq_trivial :
    hull (⊤ : Subring (Zp X)) (L X) = hull (⊤ : Subring (Zp X)) (L X) :=
  inner_outer_hull_certificate (L X) (L X) (L X) le_rfl le_rfl rfl

/-- Exact missing source data: an actual finite action `S` on this block and
a finite-level over-approximation `K_N`, both preserving the actual lattice
and coming from the Ind2 source construction. -/
def MissingActualBlockSourceAction (X : N8NativeInput l) : Prop :=
  ∃ (S : Set ((Kf X) ≃ₗ[Zp X] (Kf X))),
    (∀ s ∈ S, Submodule.map (s : Kf X →ₗ[Zp X] (Kf X)) (L X) = L X) ∧
    Nonempty S

end LeanFormal.IUT.N8Closure.FiniteObservationBlockActual