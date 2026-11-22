import tmp.sheaf.n8.closure.EtaPermittedSActual

noncomputable section

namespace ABCBridge.N8.EtaActionNonconstantAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open ABCBridge.N8.EtaPermittedSActual
open ABCBridge.N8.EtaSourceActionConcrete
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint C4.place.v)

/-! ## Exact witness for movement -/

/-- If an actual point of the source region is moved outside the region by
`ind1 g`, the action set is not equal to the original region.  This is the
exact actual sufficient condition. -/
theorem etaAction_ne_of_witness (g : Label)
    (S : Set (I.ThetaPilotPoint C4.place.v)) {y : I.ThetaPilotPoint C4.place.v}
    (hyS : y ∈ S)
    (hyout : (C4.ind.ind1 g) y ∉ S) :
    etaAction (C4 := C4) g S ≠ S := by
  intro h
  have hy : (C4.ind.ind1 g) y ∈ etaAction (C4 := C4) g S := ⟨y, hyS, rfl⟩
  rw [h] at hy
  exact hyout hy

/-- Exact equality criterion: image equals the region iff every point of the
image lies in the region and every region point is in the image. -/
theorem etaAction_eq_iff (g : Label)
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    etaAction (C4 := C4) g S = S ↔
      (∀ y, y ∈ etaAction (C4 := C4) g S → y ∈ S) ∧
        (∀ y, y ∈ S → y ∈ etaAction (C4 := C4) g S) := by
  constructor
  · intro h
    constructor
    · intro y hy; rwa [h] at hy
    · intro y hy; rwa [h]
  · rintro ⟨h1, h2⟩
    ext y
    exact ⟨h1 y, h2 y⟩

/-! ## Decisive no-go: the identity action fixes every region -/

theorem etaAction_one_fixes
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    etaAction (C4 := C4) 1 S = S :=
  etaAction_one (C4 := C4) S

/-- The universal statement that every label moves every region is false:
the identity label fixes it. -/
theorem etaAction_not_forced
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    ¬ ∀ g : Label, etaAction (C4 := C4) g S ≠ S := by
  intro h
  exact h 1 (etaAction_one_fixes (C4 := C4) S)

/-- If the label group is a subsingleton, no actual label can move the
region; the nonconstant target is impossible. -/
theorem etaAction_nonconstant_false_of_subsingleton
    [Subsingleton Label]
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    ¬ EtaActionOutputNonconstant (C4 := C4) S := by
  rintro ⟨g, hg⟩
  have hg1 : g = 1 := Subsingleton.elim g 1
  subst hg1
  exact hg (etaAction_one_fixes (C4 := C4) S)

/-- If the Ind1 homomorphism is the identity homomorphism on the label
group, every region is fixed by every label. -/
theorem etaAction_fixed_of_ind1_identity
    (h : C4.ind.ind1 = 1)
    (S : Set (I.ThetaPilotPoint C4.place.v)) (g : Label) :
    etaAction (C4 := C4) g S = S := by
  have hg : C4.ind.ind1 g = 1 := by
    simpa using congrFun (congrArg (fun f : Label →* Equiv.Perm
      (I.ThetaPilotPoint C4.place.v) => (f : Label → Equiv.Perm _)) h) g
  simp [etaAction, hg]

/-! ## Exact no-go summary -/

/-- Exact no-go condition: no production C4 field forces `ind1 g` to move
the actual source region.  A move requires the concrete witness in
`etaAction_ne_of_witness`; without it the action may be fixed. -/
def EtaActionMoveObligation
    (g : Label) (S : Set (I.ThetaPilotPoint C4.place.v)) : Prop :=
  ∃ y : I.ThetaPilotPoint C4.place.v,
    y ∈ S ∧ (C4.ind.ind1 g) y ∉ S

theorem etaActionMoveObligation_sufficient (g : Label)
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    EtaActionMoveObligation (C4 := C4) g S →
      etaAction (C4 := C4) g S ≠ S := by
  rintro ⟨y, hyS, hyout⟩
  exact etaAction_ne_of_witness (C4 := C4) g S hyS hyout

end ABCBridge.N8.EtaActionNonconstantAttempt
