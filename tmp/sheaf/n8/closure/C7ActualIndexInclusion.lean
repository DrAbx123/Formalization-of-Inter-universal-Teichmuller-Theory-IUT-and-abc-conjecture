import tmp.sheaf.n8.closure.O3ConstructedComparison
import tmp.sheaf.n8.closure.EtaTensorZpSubmoduleLatticeActual

/-!
# C7 actual index inclusion

Actual constructions:

* Lu subset Lv(g0) for g0 = fPlaceP^-1: for o in the completion integers,
  o = g0 * (fPlaceP * o) and fPlaceP * o is again integral.
* hence LuSub <= LvSub(g0) as actual Z_p-submodules.
* the actual relative index edgeIndex = relIndex LuSub LvSub(g0) gives the
  multiplier exponent d, with candidate A = log(edgeIndex).

The remaining exact comparison law

  hTensor - d * Q = 0 - A

is recorded as MissingEdgeComparisonLaw; it is not an arbitrary divisor or
constant.  No such proof is supplied by production.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.O3ConstructedComparison
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

namespace LeanFormal.IUT.N8Closure.C7ActualIndexInclusion

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

noncomputable def Q : Real := O3Q X
noncomputable def hTensor : Real := O3HTensor X

theorem Lu_subset_Lv_g0 :
    forall y : E X, y ∈ Lu X -> y ∈ Lv X (gNonIntegral X) := by
  rintro y ⟨o, rfl⟩
  refine ⟨fPlacePInt X * o, ?_⟩
  change PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => gNonIntegral X *
        ((fPlacePInt X * o : Integers (EtaTensorGraphEdgeActual.Kf X)) :
          EtaTensorGraphEdgeActual.Kf X)) =
    PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => (o : EtaTensorGraphEdgeActual.Kf X))
  congr 1
  funext _
  rw [gNonIntegral]
  change (fPlaceP X)⁻¹ * (fPlaceP X * (o : EtaTensorGraphEdgeActual.Kf X)) = (o : EtaTensorGraphEdgeActual.Kf X)
  rw [← mul_assoc, inv_mul_cancel₀ (fPlaceP_ne_zero X), one_mul]

theorem LuSub_le_LvSub_g0 :
    LuSub X ≤ LvSub X (gNonIntegral X) := by
  rw [LuSub, LvSub]
  apply Submodule.span_le.mpr
  intro y hy
  exact Submodule.subset_span (Lu_subset_Lv_g0 X y hy)

noncomputable def edgeIndex : Nat :=
  (LuSub X).toAddSubgroup.relIndex (LvSub X (gNonIntegral X)).toAddSubgroup

noncomputable def AIndex : Real := Real.log (edgeIndex X)

def MissingEdgeComparisonLaw : Prop :=
  hTensor X - (edgeIndex X : Real) * Q X = 0 - AIndex X

structure C7ActualIndexData where
  d : Nat
  d_eq : d = edgeIndex X
  A : Real
  A_eq : A = AIndex X
  Z : Real
  Z_eq : Z = 0
  law : hTensor X - (d : Real) * Q X = Z - A

def MissingC7ActualIndexComparison : Prop := Nonempty (C7ActualIndexData X)

end LeanFormal.IUT.N8Closure.C7ActualIndexInclusion
