import tmp.sheaf.n8.closure.TargetSignature
import tmp.sheaf.n8.closure.SourceInputBinding
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

/-!
# C0 base: no-go audit and corrected-target boundary

Audit result: TargetSignature.N8TargetOutput is too strong for arbitrary
OriginalInput.

The field hull_finite asserts finiteness of the value-realized source hull
sourceHullVolume.  Under pointwise degree faithfulness the production theorem
sourceHullVolume_eq_top_of_degreeFaithful proves that volume is top, so
hull_finite is impossible.  More basically, the place field already requires a
SourceInputBinding, whose existence is not constructed; and realization needs an
actual SourceTheorem311Realization.

This file records the exact no-go theorem and the corrected target boundary.
No production file is changed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C0Base

universe ua uv upi umon ui u v w uW

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.TargetSignature
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]

/-- The zero procession index. -/
def zeroPilot : ThetaPilotCarrier l := Fin.mk 0 (Nat.succ_pos _)

/-- No-go: any N8TargetOutput whose selected realization is pointwise
degree-faithful is impossible, because its hull_finite field contradicts the
proved sourceHullVolume = top. -/
theorem no_targetOutput_of_degreeFaithful
    (I : N8TargetInput (l := l) (V := V) (Label := Label) (Choice := Choice))
    (O : N8TargetOutput (l := l) (V := V) (Label := Label) (Choice := Choice) I)
    (hdeg : ∀ b : Real,
      I.I.logDegreeAt 0 0 O.place.place.selected
        (O.place.place.selected_realization.posRealAction
          (Multiplicative.ofAdd b)) = b) : False := by
  have htop : I.I.sourceHullVolume O.place.place.selected
      O.place.place.selected_realization (zeroPilot (l := l)) = ⊤ :=
    I.I.sourceHullVolume_eq_top_of_degreeFaithful O.place.place.selected
      O.place.place.selected_realization (zeroPilot (l := l)) hdeg
  have hfin : I.I.sourceHullVolume O.place.place.selected
      O.place.place.selected_realization (zeroPilot (l := l)) < ⊤ :=
    O.hull_finite (zeroPilot (l := l)) (zeroSignedLabel (l := l))
  rw [htop] at hfin
  exact (lt_irrefl (⊤ : ENNReal)) hfin

/-- No-go in the other direction: if the input has no C1 binding, no
N8TargetOutput exists, since its place field is a SourceInputBinding. -/
theorem no_targetOutput_of_no_sourceInputBinding
    (I : N8TargetInput (l := l) (V := V) (Label := Label) (Choice := Choice))
    (h : ¬ Nonempty (SourceInputBinding I.I)) :
    IsEmpty (N8TargetOutput (l := l) (V := V) (Label := Label) (Choice := Choice) I) := by
  refine ⟨fun O => h ⟨O.place⟩⟩

/-- Corrected C0 target boundary: source-hull finiteness can only be asserted
relative to the paper's compactness/hull-bound donor, not unconditionally.  The
corrected target must add an explicit hull log-degree bound (or use the actual
C7 IQ hull data) and must construct the C1 place binding and the actual
SourceTheorem311Realization. -/
def SourceHullLogBound
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  ∃ C : Real, ∀ x : I.ThetaPilotPoint v,
    x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      I.sourceLocalLogDegree v x ≤ C

/-- The corrected target carries the compactness/hull-bound premise explicitly
instead of claiming unconditional finiteness of sourceHullVolume. -/
structure C0CorrectedOutput
    (I : N8TargetInput (l := l) (V := V) (Label := Label) (Choice := Choice)) where
  place : SourceInputBinding I.I
  realization : SourceTheorem311Realization.{u, v, uW} l Label Choice
  hull_bound : ∀ (n : ThetaPilotCarrier l),
    SourceHullLogBound I.I place.place.selected
      place.place.selected_realization n
  qPilot_mem_hull : ∀ (n : ThetaPilotCarrier l) (j : SignedLabel l.value),
    I.I.sourceThetaPilotPoint place.place.selected
        place.place.selected_realization n j ∈
      (I.I.sourceHolomorphicHull place.place.selected
        place.place.selected_realization n : Set (I.I.ThetaPilotPoint place.place.selected))

end LeanFormal.IUT.N8Closure.C0Base
