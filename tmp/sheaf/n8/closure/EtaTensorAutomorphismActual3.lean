import tmp.sheaf.n8.closure.EtaTensorGraphCertificateActual
import tmp.sheaf.n8.closure.EtaTensorAutomorphismInterfaceActual

/-!
# EtaTensorAutomorphismActual3

Transport of the `Kf` multiplication equivalence to the one-factor tensor via
`PiTensorProduct.subsingletonEquiv`.  The construction and coercion theorem
are explicit; the single missing input is the naturality identity
`tau (T_g x) = g * tau x`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

noncomputable def tau : E X ≃ₗ[ℚ_[nativePrime X]] Kf X :=
  PiTensorProduct.subsingletonEquiv (R := ℚ_[nativePrime X]) (s := A X) ()

theorem tau_tprod_actual3 (f : (i : Unit) → A X i) :
    tau X (PiTensorProduct.tprod (ℚ_[nativePrime X]) f) = f () :=
  PiTensorProduct.subsingletonEquiv_apply_tprod () f

theorem graphAction_tprod_actual3 (g : Kf X) (f : (i : Unit) → A X i) :
    graphAction X g (PiTensorProduct.tprod (ℚ_[nativePrime X]) f) =
      PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g) *
        PiTensorProduct.tprod (ℚ_[nativePrime X]) f := by
  rw [graphAction, tensorActionMul, LinearMap.mulLeft_apply]
  congr 1

theorem tau_graphAction_tprod_actual3 (g : Kf X) (f : (i : Unit) → A X i) :
    tau X (graphAction X g (PiTensorProduct.tprod (ℚ_[nativePrime X]) f)) =
      g * tau X (PiTensorProduct.tprod (ℚ_[nativePrime X]) f) := by
  rw [graphAction_tprod_actual3, PiTensorProduct.tprod_mul_tprod,
    tau_tprod_actual3, tau_tprod_actual3]
  rfl

theorem tau_graphAction_obligation (g : Kf X) (x : E X) :
    tau X (graphAction X g x) = g * tau X x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [LinearMap.map_smul (graphAction X g) r
        (PiTensorProduct.tprod (ℚ_[nativePrime X]) f)]
      conv_lhs => rw [(tau X).map_smul]
      conv_rhs => rw [(tau X).map_smul]
      rw [tau_graphAction_tprod_actual3]
      rw [mul_smul_comm]
  | add x y hx hy =>
      have h := (tau X).map_add x y
      have h2 := (tau X).map_add ((graphAction X g) x) ((graphAction X g) y)
      rw [(graphAction X g).map_add x y, h2, h, hx, hy, mul_add]

noncomputable def mulEquiv (g : Kf X) (hg : g ≠ 0) : Kf X ≃ₗ[ℚ_[nativePrime X]] Kf X :=
  (Units.mk0 g hg).mulLeftLinearEquiv (ℚ_[nativePrime X]) (Kf X)

noncomputable def graphEquiv (g : Kf X) (hg : g ≠ 0) : E X ≃ₗ[ℚ_[nativePrime X]] E X :=
  (tau X).trans ((mulEquiv X g hg).trans (tau X).symm)

theorem graphEquiv_apply (g : Kf X) (hg : g ≠ 0) (x : E X) :
    graphEquiv X g hg x = (tau X).symm (g * tau X x) := by
  simp only [graphEquiv, LinearEquiv.trans_apply, mulEquiv,
    Units.mulLeftLinearEquiv_apply, Units.val_mk0]

theorem graphEquiv_coe (g : Kf X) (hg : g ≠ 0) :
    (graphEquiv X g hg : E X →ₗ[ℚ_[nativePrime X]] E X) = graphAction X g := by
  apply LinearMap.ext
  intro x
  change graphEquiv X g hg x = graphAction X g x
  rw [graphEquiv_apply]
  rw [← tau_graphAction_obligation X g x]
  exact (tau X).symm_apply_apply (graphAction X g x)

theorem tensorAutomorphismTarget_actual :
    ∃ (e : E X ≃ₗ[ℚ_[nativePrime X]] E X),
      (e : E X →ₗ[ℚ_[nativePrime X]] E X) = edgeAction X :=
  ⟨graphEquiv X (gNonIntegral X) (gNonIntegral_ne_zero X), by
    rw [graphEquiv_coe]
    exact edgeAction_eq_graphAction X⟩

end LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3