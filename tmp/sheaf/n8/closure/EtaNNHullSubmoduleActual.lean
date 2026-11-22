import tmp.sheaf.n8.closure.EtaNNHullVolumeEqualityActual

/-!
# EtaNNHullSubmoduleActual

Target: `Lv(g^k)` is a `ℤ_[p]`-submodule, so its span does not enlarge it and
the finite hull volume equality follows from monotonicity.

Actual monotonicity is re-exported.  The exact missing structure is an
`SMul/Module ℤ_[p] (Integers Kf)` compatible with the `Kf` scalar action;
`Submodule.restrictScalars` does not synthesize it.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNNHullSubmoduleActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorStandardBorelActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeActual
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev g0 : Kf X := gNonIntegral X

local instance : Module (ℤ_[nativePrime X]) (Kf X) :=
  Module.compHom (Kf X) (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]))

local instance : Module (ℤ_[nativePrime X]) (E X) :=
  Module.compHom (E X) (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]))

local instance : MeasurableSpace (E X) :=
  MeasurableSpace.map (tau X).symm (inferInstance : MeasurableSpace (Kf X))

theorem nnLattice_mono_g0_reexport (n : ℕ) :
    nnLattice X (g0 X) n ⊆ nnLattice X (g0 X) (n + 1) :=
  nnLattice_mono_g0 X n

/-- Exact missing integers submodule structure. -/
def MissingIntegersZpSubmodule (X : N8NativeInput l) : Prop :=
  ∃ L : Submodule (ℤ_[nativePrime X]) (Kf X),
    (L : Set (Kf X)) = (Integers (Kf X) : Set (Kf X))

/-- Exact missing lattice-submodule assertion: each `Lv(g^k)` is itself a
`ℤ_[p]`-submodule (not merely a set span). -/
def MissingLvSubmodule (X : N8NativeInput l) : Prop :=
  ∀ (g : Kf X) (k : ℕ),
    ∃ L : Submodule (ℤ_[nativePrime X]) (E X),
      (L : Set (E X)) = nnLattice X g k

end LeanFormal.IUT.N8Closure.EtaNNHullSubmoduleActual