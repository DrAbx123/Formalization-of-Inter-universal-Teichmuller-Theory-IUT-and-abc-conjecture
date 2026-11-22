import tmp.sheaf.n8.closure.EtaTensorAutomorphismActual3
import tmp.sheaf.n8.closure.EtaTensorAutomorphismInterfaceActual

/-!
# EtaTensorNaturalityActual

Naturality of `PiTensorProduct.subsingletonEquiv` for `tensorActionMul`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual

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
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem tau_tprod (f : (i : Unit) → A X i) :
    tau X (PiTensorProduct.tprod (ℚ_[nativePrime X]) f) = f () :=
  PiTensorProduct.subsingletonEquiv_apply_tprod () f

theorem graphAction_tprod (g : Kf X) (f : (i : Unit) → A X i) :
    graphAction X g (PiTensorProduct.tprod (ℚ_[nativePrime X]) f) =
      PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g) *
        PiTensorProduct.tprod (ℚ_[nativePrime X]) f := by
  rw [graphAction, tensorActionMul, LinearMap.mulLeft_apply]
  congr 1

theorem tau_graphAction_tprod (g : Kf X) (f : (i : Unit) → A X i) :
    tau X (graphAction X g (PiTensorProduct.tprod (ℚ_[nativePrime X]) f)) =
      g * tau X (PiTensorProduct.tprod (ℚ_[nativePrime X]) f) := by
  rw [graphAction_tprod, PiTensorProduct.tprod_mul_tprod, tau_tprod, tau_tprod]
  rfl

theorem tau_graphAction_actual (g : Kf X) (x : E X) :
    tau X (graphAction X g x) = g * tau X x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [LinearMap.map_smul (graphAction X g) r
        (PiTensorProduct.tprod (ℚ_[nativePrime X]) f)]
      conv_lhs => rw [(tau X).map_smul]
      conv_rhs => rw [(tau X).map_smul]
      rw [tau_graphAction_tprod]
      rw [mul_smul_comm]
  | add x y hx hy =>
      have h := (tau X).map_add x y
      have h2 := (tau X).map_add ((graphAction X g) x) ((graphAction X g) y)
      rw [(graphAction X g).map_add x y, h2, h, hx, hy, mul_add]

theorem graphEquiv_coe_actual (g : Kf X) (hg : g ≠ 0) :
    (EtaTensorAutomorphismActual3.graphEquiv X g hg :
      E X →ₗ[ℚ_[nativePrime X]] E X) = graphAction X g := by
  apply LinearMap.ext
  intro x
  change EtaTensorAutomorphismActual3.graphEquiv X g hg x = graphAction X g x
  rw [EtaTensorAutomorphismActual3.graphEquiv_apply]
  rw [← tau_graphAction_actual X g x]
  exact (tau X).symm_apply_apply (graphAction X g x)

theorem tensorAutomorphismTarget_actual2 :
    ∃ (e : E X ≃ₗ[ℚ_[nativePrime X]] E X),
      (e : E X →ₗ[ℚ_[nativePrime X]] E X) = edgeAction X :=
  ⟨EtaTensorAutomorphismActual3.graphEquiv X (gNonIntegral X) (gNonIntegral_ne_zero X), by
    rw [graphEquiv_coe_actual]
    exact edgeAction_eq_graphAction X⟩

end LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual