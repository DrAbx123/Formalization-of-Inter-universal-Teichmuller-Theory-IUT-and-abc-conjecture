import tmp.sheaf.n8.closure.EtaTensorGraphEdgeActual

/-!
# EtaTensorLatticeImageActual

Actual tensor lattice images: embed the completion integers (and `g *`
integers) into the one-factor tensor block via `PiTensorProduct.tprod`, and
prove the actual edge `T_g Lu ≤ Lv` using `tprod_mul_tprod`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

def Lu : Set (E X) :=
  Set.range (fun x : Integers (Kf X) =>
    PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => (x : Kf X)))

def Lv (g : Kf X) : Set (E X) :=
  Set.range (fun x : Integers (Kf X) =>
    PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => g * (x : Kf X)))

theorem tensorEdge_actual (g : Kf X) :
    GraphEdge X g (Lu X) (Lv X g) := by
  rintro y ⟨x, rfl⟩
  change graphAction X g
    (PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => (x : Kf X))) ∈
      Lv X g
  refine ⟨x, ?_⟩
  rw [graphAction, tensorActionMul]
  change PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g * (x : Kf X)) =
    PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g) *
      PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => (x : Kf X))
  rw [PiTensorProduct.tprod_mul_tprod]
  congr 1

theorem nonTrivialTensorEdge_actual :
    GraphEdge X (gNonIntegral X) (Lu X) (Lv X (gNonIntegral X)) :=
  tensorEdge_actual X (gNonIntegral X)

theorem tensorEdge_actual_nonempty :
    (Lu X).Nonempty :=
  ⟨PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => (1 : Kf X)),
    ⟨1, by simp⟩⟩

end LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual