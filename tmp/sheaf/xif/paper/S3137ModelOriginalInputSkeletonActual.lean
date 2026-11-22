import tmp.sheaf.xif.paper.S3137ModelTheaterSkeletonActual
import LeanFormal.IUT.Audit.Status

/-! # S3137: model OriginalInput skeleton (from-scratch model, task-72)

Assembles the OriginalInput skeleton from the model theater-family data:
OriginalInput = initial SourceDefinition31Data + family + index_equiv + arithmetic
alignment.  The index_equiv is the universe-lift equivalence (constructible), the
family comes from ModelTheaterData.toFamily (distinctness supplied), and the
arithmetic alignment is supplied as the model hypothesis.  This isolates exactly
what qpilot's model must provide: an index-dependent theater family, its
distinctness, and the arithmetic alignment; no model theater value is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3137ModelOriginalInputSkeletonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual
open LeanFormal.IUT.Audit

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- Universe-lift equivalence: ULift of the model index to the source index. -/
def modelULiftEquiv : ULift.{ui} ModelIndex ≃ SourceTheorem311Index where
  toFun i := i.down
  invFun p := ULift.up p
  left_inv i := by cases i; rfl
  right_inv p := rfl

/-- Construct the model OriginalInput from: the initial arithmetic data, theater
family skeleton data, distinctness of the theater, and the arithmetic alignment. -/
noncomputable def modelOriginalInputOfSkeleton
    (initial : SourceDefinition31Data.{ua} l)
    (M : ModelTheaterData.{ua, uv, upi, umon, ui} (l := l) (V := V))
    (hInj : Function.Injective M.theater)
    (hAlign : ∀ i, (M.theater i).arithmetic = initial.arithmetic) :
    OriginalInput.{ua, uv, upi, umon, ui} l V where
  initial := initial
  family := M.toFamily hInj
  index_equiv := modelULiftEquiv.{ui}
  arithmetic_alignment := hAlign

/-- The constructed model's theater-at data (n m : Int) is the model theater at
the lifted index. -/
theorem modelOriginalInput_theaterAt
    (initial : SourceDefinition31Data.{ua} l)
    (M : ModelTheaterData.{ua, uv, upi, umon, ui} (l := l) (V := V))
    (hInj : Function.Injective M.theater)
    (hAlign : ∀ i, (M.theater i).arithmetic = initial.arithmetic)
    (n m : Int) :
    (modelOriginalInputOfSkeleton initial M hInj hAlign).theaterAt n m =
      M.theater (modelULiftEquiv.{ui}.symm ((n, m) : SourceTheorem311Index)) :=
  rfl

end LeanFormal.IUT.XiFPaper.S3137ModelOriginalInputSkeletonActual

namespace LeanFormal.IUT.Audit

/-- INDEX: model OriginalInput skeleton (assembled conditional construction). -/
def S3137ModelOriginalInputRecord : Obligation :=
  { id := "INDEX.MODEL.from-scratch-original-input"
    source := "IUT I Definition 3.1; SourceOriginalInput.lean:41-46"
    status := VerificationStatus.interface
    note := "CONSTRUCTED CONDITIONAL: modelOriginalInputOfSkeleton assembles OriginalInput from initial SourceDefinition31Data + ModelTheaterData + distinctness + arithmetic alignment; index_equiv = Equiv.ulift.symm (constructible, no choice); family from ModelTheaterData.toFamily. EXACT MODEL-SIDE INPUTS: index-dependent theater value, its distinctness, arithmetic alignment (qpilot model assembly). Not a residual by itself."
    dependsOn := ["S3137ModelOriginalInputSkeletonActual", "INDEX.MODEL.from-scratch-theater-family"] }

end LeanFormal.IUT.Audit