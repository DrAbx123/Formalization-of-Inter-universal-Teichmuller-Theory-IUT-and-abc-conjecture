import tmp.sheaf.n8.closure.EtaTensorGraphOrbitSaturation

/-!
# EtaOrbitSaturationEqualityActual

Reverse inclusion for orbit saturation: every generator `L_n` is hit by
`T_g` from `L_{n-1}` using `g^n = g * g^{n-1}`.  Hence the orbit span is an
actual fixed point.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaOrbitSaturationEqualityActual

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
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphOrbitSaturation
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem graphAction_tprod_eq (a g : Kf X) (o : Integers (Kf X)) :
    graphAction X g (PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => a * (o : Kf X))) =
    PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => (g * a) * (o : Kf X)) := by
  rw [graphAction, tensorActionMul, LinearMap.mulLeft_apply]
  change PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g) *
      PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => a * (o : Kf X)) =
    PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => (g * a) * (o : Kf X))
  rw [PiTensorProduct.tprod_mul_tprod]
  congr 1
  funext i
  simp only [Pi.mul_apply]
  ring

theorem orbitSet_subset_image (g : Kf X) (hg : g ≠ 0) :
    orbitSet X g ⊆ (EtaTensorGraphOrbitSaturation.edgeZp X g hg) '' orbitSet X g := by
  rintro y hy
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  rcases hn with ⟨o, rfl⟩
  let z : E X := PiTensorProduct.tprod (ℚ_[nativePrime X])
    (fun _ : Unit => g ^ (n - 1) * (o : Kf X))
  refine ⟨z, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨n - 1, ⟨o, rfl⟩⟩
  · change (graphEquiv X g hg) z =
      PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g ^ n * (o : Kf X))
    rw [show (graphEquiv X g hg) z = graphAction X g z from
      DFunLike.congr_fun (graphEquiv_coe_actual X g hg) z]
    rw [graphAction_tprod_eq]
    congr 1
    funext i
    rw [zpow_sub_one₀ hg]
    field_simp [hg]

theorem orbitSub_le_map (g : Kf X) (hg : g ≠ 0) :
    orbitSub X g ≤ Submodule.map (EtaTensorGraphOrbitSaturation.edgeZp X g hg) (orbitSub X g) := by
  rw [orbitSub, Submodule.map_span]
  exact Submodule.span_mono (orbitSet_subset_image X g hg)

theorem orbitSaturationEquality_actual (g : Kf X) (hg : g ≠ 0) :
    OrbitSaturationEquality X g hg :=
  le_antisymm (edgeZp_maps_orbit X g hg) (orbitSub_le_map X g hg)

end LeanFormal.IUT.N8Closure.EtaOrbitSaturationEqualityActual