import tmp.sheaf.n8.closure.C4IndActionPaperAttempt
import tmp.sheaf.n8.closure.C5SHEIntegration

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperC4IndBridgeActualAttempt

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.C4IndActionPaperAttempt
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I
  (Multiplicative (finiteLabel l)))

/-! ## Actual bridge in the canonical label case -/

/-- Actual paper-to-C4 bridge when the C4 label group is the finite label
group itself: the paper finite-label action is `paperLabelIndData`, the label
map is the canonical `Multiplicative.ofAdd`, and the C4 action is the actual
`C4.ind.ind1` supplied by the C4 record.  This is not an arbitrary bridge. -/
noncomputable def actualPaperC4IndBridge :
    PaperC4IndBridge (l := l) (V := V) I (LAdd := finiteLabel l) C4 where
  paper := paperLabelIndData l
  labelMap := fun t => Multiplicative.ofAdd t
  c4Action := C4.ind.ind1

theorem actualPaperC4IndBridge_nonempty :
    Nonempty (PaperC4IndBridge (l := l) (V := V) I (LAdd := finiteLabel l) C4) :=
  ⟨actualPaperC4IndBridge (l := l) (V := V) I C4⟩

/-- The second actual C4 Ind action gives the same bridge shape. -/
noncomputable def actualPaperC4IndBridgeInd2 :
    PaperC4IndBridge (l := l) (V := V) I (LAdd := finiteLabel l) C4 where
  paper := paperLabelIndData l
  labelMap := fun t => Multiplicative.ofAdd t
  c4Action := C4.ind.ind2

theorem actualPaperC4IndBridgeInd2_nonempty :
    Nonempty (PaperC4IndBridge (l := l) (V := V) I (LAdd := finiteLabel l) C4) :=
  ⟨actualPaperC4IndBridgeInd2 (l := l) (V := V) I C4⟩

/-! ## Exact general no-go -/

/-- In the general C4 case the label map `finiteLabel l -> Multiplicative LAdd`
is not supplied by C4 or LabelData; a bridge for arbitrary `LAdd` would have to
invent it.  This is the exact no-go boundary, recorded as an equivalence to
supplying the two bridge components. -/
theorem PaperC4IndBridge_general_nonempty_iff
    {LAdd : Type*} [AddGroup LAdd]
    (C4gen : SourceWitnessedOutputData (l := l) (V := V) I
      (Multiplicative LAdd)) :
    Nonempty (PaperC4IndBridge (l := l) (V := V) I (LAdd := LAdd) C4gen) ↔
      ∃ (labelMap : finiteLabel l → Multiplicative LAdd)
        (c4Action : Multiplicative LAdd →*
          Equiv.Perm (I.ThetaPilotPoint C4gen.place.v)), True := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.labelMap, B.c4Action, trivial⟩
  · rintro ⟨labelMap, c4Action, _⟩
    exact ⟨{ paper := paperLabelIndData l, labelMap := labelMap, c4Action := c4Action }⟩

end LeanFormal.IUT.N8Closure.PaperC4IndBridgeActualAttempt
