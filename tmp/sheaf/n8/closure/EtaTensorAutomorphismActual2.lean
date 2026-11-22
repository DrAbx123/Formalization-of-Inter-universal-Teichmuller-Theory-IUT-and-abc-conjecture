import tmp.sheaf.n8.closure.EtaTensorGraphCertificateActual

/-!
# EtaTensorAutomorphismActual2

Attempt to construct the tensor automorphism from a unit.  Exact blocker:
the one-factor `PiTensorProduct` type `E` has no `GroupWithZero`/unit
structure registered, so `Units.mulLeftLinearEquiv` cannot be applied
directly; the necessary `PiTensorProduct.subsingletonEquiv` naturality lemma
for `tensorActionMul` is also absent.  The nonzero scalar and set certificate
remain actual; no arbitrary automorphism is added.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual2

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem gNonIntegral_ne_zero : gNonIntegral X ≠ 0 :=
  inv_ne_zero (fPlaceP_ne_zero X)

theorem edgeAction_eq_graphAction :
    edgeAction X = graphAction X (gNonIntegral X) := rfl

theorem tensorSetHullCertificate_reexport : TensorSetHullCertificate X :=
  tensorSetHullCertificate_actual X

/-- Exact missing tensor algebra/unit structure on the one-factor tensor. -/
def MissingTensorUnitStructure (X : N8NativeInput l) : Prop :=
  Nonempty (GroupWithZero (E X))

/-- Exact automorphism target with coercion equal to the actual edge action. -/
def TensorAutomorphismTarget (X : N8NativeInput l) : Prop :=
  ∃ (e : E X ≃ₗ[ℚ_[nativePrime X]] E X),
    (e : E X →ₗ[ℚ_[nativePrime X]] E X) = edgeAction X

end LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual2