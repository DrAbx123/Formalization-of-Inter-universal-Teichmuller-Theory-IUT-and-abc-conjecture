import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingClosure
import tmp.sheaf.n8.closure.EtaDVRInstanceActual
import tmp.sheaf.n8.closure.EtaUnitHaarInvarianceAttempt

noncomputable section
namespace LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaActual3
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
open LeanFormal.IUT.N8Closure.EtaDVRInstanceActual
open LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingClosure
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory Metric
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem integers_interior_nonempty :
    (interior (Integers (Kf X) : Set (Kf X))).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  refine _root_.mem_nhds_iff.mpr ⟨ball (0 : Kf X) 1, ?_, isOpen_ball,
    mem_ball_self one_pos⟩
  intro x hx
  exact (LeanFormal.IUT.LocalFieldIntegralUnits.mem_integers_iff (K := Kf X) x).mpr
    (le_of_lt (by simpa using hx))

theorem addHaar_O_pos :
    0 < (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) :=
  Measure.measure_pos_of_nonempty_interior _ (integers_interior_nonempty X)

theorem addHaar_O_finite :
    (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) < ∞ := by
  haveI : CompactSpace (Integers (Kf X)) :=
    EtaDVRInstanceActual.integersCompactSpace (X := X)
  have hsub : IsCompact (Set.univ : Set (Integers (Kf X))) := isCompact_univ
  have hK : IsCompact (Integers (Kf X) : Set (Kf X)) := by
    simpa using hsub.image continuous_subtype_val
  exact hK.measure_lt_top (μ := (Measure.addHaar : Measure (Kf X)))

end LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaActual3