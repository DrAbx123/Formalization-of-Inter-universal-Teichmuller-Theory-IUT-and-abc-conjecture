/-
# C4 stage 2, non-Group parallel label version

`SourceWitnessedOutput.lean` currently uses a provisional `[Group Label]`
binder.  The paper label object is `LabelData.LabelData`: a finite label set
with an arbitrary `Equiv.Perm` automorphism, not a group.  This file supplies a
parallel non-Group interface `SourceWitnessedOutputDataPerm` without weakening or
enlarging the source condition: all Ind actions are plain maps
`P.Labels → Equiv.Perm Y`.
-/
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.LabelData

noncomputable section

namespace ABCBridge.N8.C4Actual.NonGroup

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.LabelData
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : SourceInput (l := l) (V := V)}

/-- Non-Group Ind action data: the paper label set acts by arbitrary
permutations, with no additive/multiplicative group structure. -/
structure IndActionDataPerm (Y : Type*) (P : LabelData.{uL}) where
  ind1 : P.Labels → Equiv.Perm Y
  ind2 : P.Labels → Equiv.Perm Y
  ind3_nonarch : Nat → Set Y → Set Y
  ind3_arch : Nat → Set Y → Set Y
  ind3_nonarch_inclusion : ∀ n S, S ⊆ ind3_nonarch n S
  ind3_arch_surjection : ∀ n S, ind3_arch n S ⊆ S

/-- Parallel C4 stage-2 data using the paper finite label set + permutation
action instead of the provisional `[Group Label]`. -/
structure SourceWitnessedOutputDataPerm
    (I : SourceInput (l := l) (V := V)) (P : LabelData.{uL}) where
  place : C1PlaceData (I := I)
  pilot : C3ThetaPilotData l
  ind : IndActionDataPerm (I.ThetaPilotPoint place.v) P

namespace SourceWitnessedOutputDataPerm

variable {P : LabelData.{uL}}
variable (D : SourceWitnessedOutputDataPerm (l := l) (V := V) I P)

abbrev Choice (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) : Type _ :=
  SignedLabel l.value

def eval (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
    (c : Choice (D := D) n x) : I.ThetaPilotPoint D.place.v :=
  I.sourceThetaPilotPoint D.place.v D.place.R n c

def U (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    Set (I.ThetaPilotPoint D.place.v) :=
  {y | ∃ c : Choice (D := D) n x, eval (D := D) n x c = y}

abbrev Witness (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) : Type _ :=
  Sigma (fun c : Choice (D := D) n x =>
    {y : I.ThetaPilotPoint D.place.v // eval (D := D) n x c = y})

def witnessOutput {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}
    (w : Witness (D := D) n x) : I.ThetaPilotPoint D.place.v := w.2.1

theorem witnessOutput_eq_eval {n : ThetaPilotCarrier l}
    {x : I.ThetaPilotPoint D.place.v} (w : Witness (D := D) n x) :
    D.witnessOutput w = D.eval n x w.1 := w.2.2.symm

theorem mem_U_iff {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}
    {y : I.ThetaPilotPoint D.place.v} :
    y ∈ D.U n x ↔ ∃ c : Choice (D := D) n x, D.eval n x c = y := Iff.rfl

def ind1Image (g : P.Labels) (S : Set (I.ThetaPilotPoint D.place.v)) :
    Set (I.ThetaPilotPoint D.place.v) := (D.ind.ind1 g) '' S

def ind2Image (g : P.Labels) (S : Set (I.ThetaPilotPoint D.place.v)) :
    Set (I.ThetaPilotPoint D.place.v) := (D.ind.ind2 g) '' S

theorem ind3_nonarch_direction (n : Nat)
    (S : Set (I.ThetaPilotPoint D.place.v)) : S ⊆ D.ind.ind3_nonarch n S :=
  D.ind.ind3_nonarch_inclusion n S

theorem ind3_arch_direction (n : Nat)
    (S : Set (I.ThetaPilotPoint D.place.v)) : D.ind.ind3_arch n S ⊆ S :=
  D.ind.ind3_arch_surjection n S

end SourceWitnessedOutputDataPerm

#check IndActionDataPerm
#check SourceWitnessedOutputDataPerm
#check SourceWitnessedOutputDataPerm.U
#print axioms SourceWitnessedOutputDataPerm.witnessOutput_eq_eval
end ABCBridge.N8.C4Actual.NonGroup
end