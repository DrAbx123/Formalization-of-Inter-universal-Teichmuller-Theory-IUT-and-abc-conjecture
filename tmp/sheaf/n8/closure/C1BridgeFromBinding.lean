import tmp.sheaf.n8.closure.C1BridgeActualSource
import tmp.sheaf.n8.closure.SourceInputBinding

/-! # C1 bridge from an actual SourceInputBinding

Connects the C1 binding's selected place/realization to the actual
q/hull QHullBridge and Cor3.12 conclusion.  Conditional only on the
explicit source comparison hq; no C1 field, no axiom.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1BridgeFromBinding

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotGlobalNormalization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.C9IUTBridgeContract
open LeanFormal.IUT.N8Closure.C1BridgeActualSource

universe u v w ua uv upi umon ui ux

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]
  {R : SourceTheorem311Realization l Label Choice}
  {V : Type uv} {I : OriginalInput l V}
  (C1 : SourceInputBinding I)
  {n : ThetaPilotCarrier l}
  {k : Type ux} [Field k] [NumberField k]
  {selectedLowerPlaces : Finset (NumberField.FinitePlace k)}
  {parameters : (lowerPlace : selectedLowerPlaces) →
    FinitePlaceQCandidate lowerPlace.val}

/-- C1/Cor3.12 from an actual SourceInputBinding and the explicit q<=h comparison. -/
theorem cor312_of_source_binding
    (hne : selectedLowerPlaces.Nonempty)
    (hfin : I.sourceHullVolume C1.place.selected C1.place.selected_realization n < (⊤ : ENNReal))
    (hq : absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters <=
      (I.sourceHullVolume C1.place.selected C1.place.selected_realization n).toReal)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    Cor312Conclusion
      ((qHullBridgeOfSource (R := R) (I := I) (v := C1.place.selected)
        (Rimg := C1.place.selected_realization) (n := n)
        (selectedLowerPlaces := selectedLowerPlaces)
        (parameters := parameters) hne hfin).toStepXIContract
        hq ipl she apt ipl_evidence she_evidence apt_evidence) := by
  exact cor312_of_actual_hull_comparison (R := R) (I := I)
    (v := C1.place.selected) (Rimg := C1.place.selected_realization)
    (n := n) (selectedLowerPlaces := selectedLowerPlaces)
    (parameters := parameters) hne hfin hq ipl she apt ipl_evidence she_evidence apt_evidence

end LeanFormal.IUT.N8Closure.C1BridgeFromBinding

end