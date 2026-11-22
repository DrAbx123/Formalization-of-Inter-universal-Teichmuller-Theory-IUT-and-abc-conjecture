import tmp.sheaf.n8.closure.SourceAllowedActualDataReduction
import tmp.sheaf.n8.closure.P6Bridge
import tmp.sheaf.n8.closure.SourceInputBinding

/-!
# C4Obligation actual attempt

Target: SourceAllowedActualDataReduction.C4Obligation D, i.e.
Nonempty (SourceWitnessedOutputData (actualBridge D).input (PaperLabel l)).

Actual from the donors:
- C1PlaceData: bridge.binding.place.selected / selected_realization;
- C3ThetaPilotData: the actual zero procession carrier.

Missing actual source data:
- IndActionData on the old output carrier.  P6BridgeDonors/C1PlaceData do not
  provide Ind1/Ind2/Ind3.  Therefore the unconditional C4Obligation is not
  constructed from those donors; the exact named gap is c4IndActionData_obligation.

No free witness or Ind action is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4ObligationActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
open LeanFormal.IUT.N8Closure.SourceAllowedActualDataReduction
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- The actual zero procession of the theta-pilot carrier. -/
def zeroThetaPilotCarrier : ThetaPilotCarrier l :=
  ⟨0, Nat.succ_pos _⟩

/-- C1PlaceData from the exact old bridge binding. -/
noncomputable def c1PlaceDataOfDonors (D : P6BridgeDonors X) :
    C1PlaceData (I := (actualBridge D).input) where
  v := (actualBridge D).binding.place.selected
  R := (actualBridge D).binding.place.selected_realization

/-- Exact missing IndActionData over the old output carrier. -/
def C4IndObligation (D : P6BridgeDonors X) : Prop :=
  Nonempty (IndActionData
    ((actualBridge D).input.ThetaPilotPoint (c1PlaceDataOfDonors D).v)
    (P6Comparison.PaperLabel l))

/-- Conditional actual C4 data from an actual IndActionData. -/
noncomputable def c4DataOfInd (D : P6BridgeDonors X)
    (ind : IndActionData
      ((actualBridge D).input.ThetaPilotPoint (c1PlaceDataOfDonors D).v)
      (P6Comparison.PaperLabel l)) :
    SourceWitnessedOutputData (actualBridge D).input
      (P6Comparison.PaperLabel l) where
  place := c1PlaceDataOfDonors D
  pilot := ⟨zeroThetaPilotCarrier (l := l)⟩
  ind := ind

/-- C4Obligation from the exact Ind obligation. -/
theorem c4Obligation_of_ind (D : P6BridgeDonors X)
    (h : C4IndObligation D) : C4Obligation D := by
  obtain ⟨ind⟩ := h
  exact ⟨c4DataOfInd D ind⟩

end LeanFormal.IUT.N8Closure.C4ObligationActualAttempt
