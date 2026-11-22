import tmp.sheaf.n8.closure.EtaOrbitSaturationEqualityActual
import tmp.sheaf.n8.closure.EtaTensorAutomorphismInterfaceActual

/-!
# EtaOrbitFiniteLevelKN

Attempt to construct a finite-level `K_N` and the outer lattice for the
actual orbit.  The actual orbit span is saturated under `g`, but no finite
quotient lattice / finite image `K_N` is present in the tree.  The exact
structure and conditional Theorem C certificate are recorded.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaOrbitFiniteLevelKN

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphOrbitSaturation
open LeanFormal.IUT.N8Closure.EtaOrbitSaturationEqualityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

abbrev g0 : Kf X := gNonIntegral X
theorem g0_ne_zero : g0 X ≠ 0 := gNonIntegral_ne_zero X

/-- Exact finite-level data: a finite subgroup of `ℤ_[p]`-linear
automorphisms preserving the actual orbit span and containing the actual
edge action.  This is the missing `K_N`. -/
structure KNActionOnOrbit (X : N8NativeInput l) (N : ℕ) where
  KN : Subgroup (E X ≃ₗ[ℤ_[nativePrime X]] E X)
  finite : Finite KN
  preserves : ∀ k : KN,
    Submodule.map ((k : E X ≃ₗ[ℤ_[nativePrime X]] E X) : E X →ₗ[ℤ_[nativePrime X]] E X) (orbitSub X (g0 X)) =
      orbitSub X (g0 X)
  contains_g : ∃ k : KN,
    ((k : E X ≃ₗ[ℤ_[nativePrime X]] E X) : E X →ₗ[ℤ_[nativePrime X]] E X) =
      EtaTensorGraphOrbitSaturation.edgeZp X (g0 X) (g0_ne_zero X)

def FiniteLevelKNTarget (X : N8NativeInput l) (N : ℕ) : Prop :=
  Nonempty (KNActionOnOrbit X N)

/-- Outer lattice from a finite-level `K_N`: since every `k` preserves the
actual orbit span, the orbit hull is the same submodule. -/
noncomputable def outerLattice {N : ℕ} (K : KNActionOnOrbit X N) :
    Submodule (ℤ_[nativePrime X]) (E X) := orbitSub X (g0 X)

theorem inner_outer_certificate_of_KN {N : ℕ} (K : KNActionOnOrbit X N) :
    InnerOuterHullCertificate (V := E X) (⊤ : Subring (ℤ_[nativePrime X]))
      (orbitSub X (g0 X)) (orbitSub X (g0 X)) (outerLattice X K) :=
  ⟨le_rfl, le_rfl, rfl⟩

end LeanFormal.IUT.N8Closure.EtaOrbitFiniteLevelKN