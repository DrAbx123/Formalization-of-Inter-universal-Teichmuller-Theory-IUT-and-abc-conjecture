import tmp.sheaf.n8.closure.EtaTensorNaturalityActual
import tmp.sheaf.n8.closure.EtaTensorGraphCertificateActual

/-!
# EtaTensorZpSubmoduleLatticeActual

Construct the `Module ℤ_[p] E` restriction and the actual `ℤ_[p]`-submodule
lattices `LuSub`, `LvSub`, together with the actual lattice edge
`edgeZp : LuSub → LvSub`.  Theorem C still needs an automorphism preserving
one common lattice; the exact gap is recorded.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

local instance : Module (ℤ_[nativePrime X]) (E X) :=
  Module.compHom (E X) (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]))

noncomputable def LuSub : Submodule (ℤ_[nativePrime X]) (E X) :=
  Submodule.span (ℤ_[nativePrime X]) (Lu X)

noncomputable def LvSub (g : Kf X) : Submodule (ℤ_[nativePrime X]) (E X) :=
  Submodule.span (ℤ_[nativePrime X]) (Lv X g)

noncomputable def edgeZp (g : Kf X) (hg : g ≠ 0) :
    E X →ₗ[ℤ_[nativePrime X]] E X where
  toFun := graphEquiv X g hg
  map_add' := (graphEquiv X g hg).map_add
  map_smul' := by
    intro a x
    change graphEquiv X g hg (a • x) = a • graphEquiv X g hg x
    rw [show a • x = (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]) a) • x
      from rfl]
    rw [show a • graphEquiv X g hg x =
      (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]) a) •
        graphEquiv X g hg x from rfl]
    exact (graphEquiv X g hg).map_smul _ x

theorem edgeZp_maps_LuSub_le_LvSub (g : Kf X) (hg : g ≠ 0) :
    Submodule.map (edgeZp X g hg) (LuSub X) ≤ LvSub X g := by
  rw [LuSub, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  have hx' : (graphEquiv X g hg) x = graphAction X g x := by
    exact DFunLike.congr_fun (graphEquiv_coe_actual X g hg) x
  change (graphEquiv X g hg) x ∈ (LvSub X g)
  rw [hx']
  exact Submodule.subset_span (tensorEdge_actual X g x hx)

/-- Exact missing preservation: Theorem C needs the edge automorphism to
preserve one common lattice (or equal hulls).  The actual edge maps `LuSub`
only into `LvSub`. -/
def MissingLatticePreservation (X : N8NativeInput l) : Prop :=
  Submodule.map (edgeZp X (gNonIntegral X) (gNonIntegral_ne_zero X)) (LuSub X) =
    LuSub X

end LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual