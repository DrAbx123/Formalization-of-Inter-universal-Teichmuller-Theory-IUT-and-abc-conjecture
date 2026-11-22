import tmp.sheaf.n8.closure.C9IUTBridgeContract

/-! # C1 bridge from actual source hull data

Builds `QHullBridge` from actual `SourceImageRealization`, actual source
hull/volume, and actual q-pilot normalization.  The only inequality input is
the explicit `hq : qPilotLog <= hullVolume.toReal`; no C1 field, no axiom.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1BridgeActualSource

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotGlobalNormalization
open LeanFormal.IUT.N8Closure.C9IUTBridgeContract

universe u v w ua uv upi umon ui ux

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]
  {R : SourceTheorem311Realization l Label Choice}
  {V : Type uv} {I : OriginalInput l V}
  {v : V} {Rimg : I.SourceImageRealization v}
  {n : ThetaPilotCarrier l}
  {k : Type ux} [Field k] [NumberField k]
  {selectedLowerPlaces : Finset (NumberField.FinitePlace k)}
  {parameters : (lowerPlace : selectedLowerPlaces) →
    FinitePlaceQCandidate lowerPlace.val}

/-- Actual QHullBridge from source hull data and a finite-volume proof. -/
def qHullBridgeOfSource
    (hne : selectedLowerPlaces.Nonempty)
    (hfin : I.sourceHullVolume v Rimg n < (⊤ : ENNReal)) :
    QHullBridge R I v Rimg n selectedLowerPlaces parameters where
  selected_nonempty := hne
  qPilotLog := absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters
  qPilotLog_source := rfl
  hull := I.sourceHolomorphicHull v Rimg n
  hull_eq := rfl
  hullVolume := I.sourceHullVolume v Rimg n
  hullVolume_eq := rfl
  hullVolume_lt_top := hfin

/-- C1/Cor3.12 bridge from the actual source hull comparison `q <= h`. -/
theorem cor312_of_actual_hull_comparison
    (hne : selectedLowerPlaces.Nonempty)
    (hfin : I.sourceHullVolume v Rimg n < (⊤ : ENNReal))
    (hq : absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters <=
      (I.sourceHullVolume v Rimg n).toReal)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    Cor312Conclusion
      ((qHullBridgeOfSource (R := R) (I := I) (v := v) (Rimg := Rimg)
        (n := n) (selectedLowerPlaces := selectedLowerPlaces)
        (parameters := parameters) hne hfin).toStepXIContract
        hq ipl she apt ipl_evidence she_evidence apt_evidence) := by
  exact QHullBridge.cor312Conclusion_toStepXIContract
    (qHullBridgeOfSource (R := R) (I := I) (v := v) (Rimg := Rimg)
      (n := n) (selectedLowerPlaces := selectedLowerPlaces)
      (parameters := parameters) hne hfin)
    hq ipl she apt ipl_evidence she_evidence apt_evidence

end LeanFormal.IUT.N8Closure.C1BridgeActualSource

end