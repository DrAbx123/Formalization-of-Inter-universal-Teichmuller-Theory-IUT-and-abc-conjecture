import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib

/-!
# C4 stage 2: source-witnessed output from the actual C0 input

This file replaces the earlier generic C0Signature schema with the actual C0-stage1
input interface:

  I : OriginalInput l V

and the C1/C3 chain data

  v : V, R : I.SourceImageRealization v, n : ThetaPilotCarrier l.

The output carrier is the actual value-point carrier I.ThetaPilotPoint v (the
candidate recorded in C4-STAGE1; G4 primary output-carrier gap remains open).

The choice family is the candidate

  C n x = SignedLabel l.value

and eval is the actual sourceThetaPilotPoint. The output region is defined as the
range of eval with a dependent-pair witness; there is no free possibleImage field.

Ind1/Ind2/Ind3 are kept as an explicit parameter structure IndActionData with real
action/set types and direction laws. No actual source instantiation of that
structure is asserted; it is the named obligation corresponding to C4-STAGE1
G2/G3. No True, PUnit, arbitrary output Type, or arbitrary Nonempty is used.

## PENDING LABEL CORRECTION (2026-10-23)

The [Group Label] parameter in this file is PROVISIONAL stage-2 scaffolding.
The paper's labels form a finite set with an Equiv.Perm action, not a Group.
Do not treat Group Label as the paper label object. The IndActionData and
SourceWitnessedOutputData group parameters below are marked to be corrected
after qside's LabelData.lean lands; at that point Ind1/Ind2 must use the finite
label set/permutation action rather than [Group Label]. No further alignment is
claimed in this file.
-/

noncomputable section

namespace ABCBridge.N8.C4Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} [Group Label]

/-- The actual source input of C4 stage 2: C0-stage1's OriginalInput. -/
abbrev SourceInput := OriginalInput.{ua, uv, upi, umon, ui} l V

/-- C1 chain data: the selected place and its actual value-group realization. -/
structure C1PlaceData (I : SourceInput (l := l) (V := V)) where
  v : V
  R : I.SourceImageRealization v

/-- C3 chain data: the theta-pilot carrier.  A selected signed label is one
choice in the output family, not a separate parameter of the region. -/
structure C3ThetaPilotData (l : PrimeGeFive) where
  n : ThetaPilotCarrier l

/-- Explicit Ind1/Ind2/Ind3 obligation at the output carrier.  The fields are
actual action/set types and direction laws; an actual source instantiation is
not asserted here (C4-STAGE1 G2/G3).

PENDING LABEL CORRECTION: the [Group Label] binder is provisional. The paper's
labels are a finite set with an Equiv.Perm action, not a Group; replace this
interface when qside's LabelData.lean lands. -/
structure IndActionData (Y : Type*) (Label : Type*) [Group Label] where
  ind1 : Label →* Equiv.Perm Y
  ind2 : Label →* Equiv.Perm Y
  ind3_nonarch : Nat → Set Y → Set Y
  ind3_arch : Nat → Set Y → Set Y
  ind3_nonarch_inclusion : ∀ n S, S ⊆ ind3_nonarch n S
  ind3_arch_surjection : ∀ n S, ind3_arch n S ⊆ S

/-- C4 stage-2 data: actual C0 input, C1 place data, C3 theta-pilot data, and
the explicit Ind obligation.

PENDING LABEL CORRECTION: the [Group Label] parameter is provisional stage-2
scaffolding, not the paper's finite label set/permutation action. Align with
qside LabelData.lean before treating the Ind action as source-correct. -/
structure SourceWitnessedOutputData
    (I : SourceInput (l := l) (V := V)) (Label : Type uL) [Group Label] where
  place : C1PlaceData (I := I)
  pilot : C3ThetaPilotData l
  ind : IndActionData (I.ThetaPilotPoint place.v) Label

namespace SourceWitnessedOutputData

variable {I : SourceInput (l := l) (V := V)}
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- The candidate choice family at index n and state x: signed labels. -/
abbrev Choice (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    Type _ :=
  SignedLabel l.value

/-- The actual source evaluation: sourceThetaPilotPoint at the C1 place and C3
carrier.  The state x is not used by the candidate choice family. -/
def eval (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
    (c : Choice (D := D) n x) : I.ThetaPilotPoint D.place.v :=
  I.sourceThetaPilotPoint D.place.v D.place.R n c

/-- The witnessed output region is the range of eval over the candidate choices. -/
def U (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    Set (I.ThetaPilotPoint D.place.v) :=
  {y | ∃ c : Choice (D := D) n x, eval (D := D) n x c = y}

/-- Dependent-pair witness retaining the actual choice. -/
abbrev Witness (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    Type _ :=
  Sigma (fun c : Choice (D := D) n x =>
    {y : I.ThetaPilotPoint D.place.v // eval (D := D) n x c = y})

/-- Output component of a witness. -/
def witnessOutput {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}
    (w : Witness (D := D) n x) : I.ThetaPilotPoint D.place.v :=
  w.2.1

/-- The witness output is the evaluation of its choice. -/
theorem witnessOutput_eq_eval {n : ThetaPilotCarrier l}
    {x : I.ThetaPilotPoint D.place.v} (w : Witness (D := D) n x) :
    D.witnessOutput w = D.eval n x w.1 :=
  w.2.2.symm

/-- Membership in U is existential existence of a choice. -/
theorem mem_U_iff {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}
    {y : I.ThetaPilotPoint D.place.v} :
    y ∈ D.U n x ↔ ∃ c : Choice (D := D) n x, D.eval n x c = y :=
  Iff.rfl

/-- U is the range of the dependent-pair witness map. -/
theorem U_eq_range (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    D.U n x = Set.range (fun w : Witness (D := D) n x => D.witnessOutput w) := by
  ext y
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, ⟨y, hc⟩⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, w.2.2⟩

/-- The candidate region is exactly the actual source possible-image union at n. -/
theorem U_eq_possibleImage (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) :
    D.U n x =
      {y | I.PossibleThetaPilotImageAt D.place.v D.place.R n y} := by
  ext y
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

/-- Ind1 image of a region, using the explicit Ind obligation. -/
def ind1Image (g : Label) (S : Set (I.ThetaPilotPoint D.place.v)) :
    Set (I.ThetaPilotPoint D.place.v) :=
  (D.ind.ind1 g) '' S

/-- Ind2 image of a region. -/
def ind2Image (g : Label) (S : Set (I.ThetaPilotPoint D.place.v)) :
    Set (I.ThetaPilotPoint D.place.v) :=
  (D.ind.ind2 g) '' S

/-- Nonarchimedean Ind3 direction (natural inclusion). -/
theorem ind3_nonarch_direction (n : Nat)
    (S : Set (I.ThetaPilotPoint D.place.v)) :
    S ⊆ D.ind.ind3_nonarch n S :=
  D.ind.ind3_nonarch_inclusion n S

/-- Archimedean Ind3 direction (natural surjection). -/
theorem ind3_arch_direction (n : Nat)
    (S : Set (I.ThetaPilotPoint D.place.v)) :
    D.ind.ind3_arch n S ⊆ S :=
  D.ind.ind3_arch_surjection n S

/-- Ind1 and Ind2 are group actions on the output carrier. -/
theorem ind1_mul (g h : Label) : D.ind.ind1 (g * h) = D.ind.ind1 g * D.ind.ind1 h :=
  map_mul D.ind.ind1 g h

theorem ind2_mul (g h : Label) : D.ind.ind2 (g * h) = D.ind.ind2 g * D.ind.ind2 h :=
  map_mul D.ind.ind2 g h

end SourceWitnessedOutputData

end ABCBridge.N8.C4Actual
