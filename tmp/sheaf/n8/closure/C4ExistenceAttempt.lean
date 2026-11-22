import tmp.sheaf.n8.closure.SourceWitnessedOutput

/-!
# C4 existence attempt: SourceWitnessedOutputData

Reuses the actual C4 file.  The structure needs:
- `place : C1PlaceData I`, i.e. an actual selected `v` and `R : I.SourceImageRealization v`;
- `pilot : C3ThetaPilotData l` (a ThetaPilotCarrier index);
- `ind : IndActionData (I.ThetaPilotPoint place.v) Label` with actual actions.

`C1PlaceData` and `IndActionData` are explicit parameters in the actual C4
stage-2 file.  No production constructor of either is found, so the full
existence is a named obligation; a conditional no-go and a zero-sorry
constructor from explicit data are provided.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4ExistenceAttempt

universe ua uv upi umon ui uL

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} [Group Label]

/-- Actual C4 structure from explicit place/pilot/Ind data; zero sorry. -/
noncomputable def sourceWitnessedOutputOfData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (place : C1PlaceData (I := I)) (pilot : C3ThetaPilotData l)
    (ind : IndActionData (I.ThetaPilotPoint place.v) Label) :
    SourceWitnessedOutputData (l := l) (V := V) I Label where
  place := place
  pilot := pilot
  ind := ind

/-- Exact missing C4 place data: selected v plus actual image realization. -/
def C4PlaceDataExists (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (C1PlaceData (I := I))

/-- Exact missing Ind1/Ind2/Ind3 action data at a C1 place. -/
def C4IndActionExists (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (place : C1PlaceData (I := I)) : Prop :=
  Nonempty (IndActionData (I.ThetaPilotPoint place.v) Label)

/-- Conditional exact no-go: if there is no C1 place datum, C4 cannot exist. -/
theorem no_sourceWitnessedOutput_of_empty_place
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (h : IsEmpty (C1PlaceData (I := I))) :
    IsEmpty (SourceWitnessedOutputData (l := l) (V := V) I Label) :=
  ⟨fun D => h.false D.place⟩

end LeanFormal.IUT.N8Closure.C4ExistenceAttempt