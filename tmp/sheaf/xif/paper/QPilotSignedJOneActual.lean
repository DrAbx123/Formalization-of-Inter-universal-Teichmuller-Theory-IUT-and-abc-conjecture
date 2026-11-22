import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import tmp.sheaf.xif.paper.SourceHullVolumeSignCorrectedActual

/-! # q-pilot signed scalar at j = 1 and its actual point log-volume

The source q-side normalized value is

  sourceQSideNormalizedValue I n j
    = card(SourceVolumeIndex l) * log (I.thetaValueAt (n.val : Int) 0 j).

At the actual label j = oneSignedLabel (the label 1 in F_l^*), this is the
q-pilot signed scalar with the same card(SourceVolumeIndex) factor as the
theta-pilot point log-volume:

  sourceLocalLogDegree v (sourceThetaPilotPoint v R n oneSignedLabel)
    = card(SourceVolumeIndex l) * log (thetaValueAt n 0 oneSignedLabel).

This file constructs the q-pilot signed scalar at j = 1 and proves the actual
equality with the signed local log-volume of the q-pilot point inside the
source holomorphic hull.  The card factor is present on both sides; no factor
is dropped and no inequality is asserted.

The full hull supremum is NOT identified with this single point value; that
would require an additional maximality theorem.  No fake equality is used.
No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.OriginalInput.QPilotSignedJOneActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)

/-- The q-pilot signed scalar at j = 1: the source q-side normalized value at
oneSignedLabel. -/
noncomputable def qPilotSignedAtOne : Real :=
  I.sourceQSideNormalizedValue n (oneSignedLabel (l := l))

/-- Explicit formula: q-pilot signed at j=1 is card * log q_v. -/
theorem qPilotSignedAtOne_eq :
    qPilotSignedAtOne I n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0
          (oneSignedLabel (l := l))) := rfl

/-- The signed local log-volume of the actual q-pilot point at j=1 inside the
source holomorphic hull. -/
noncomputable def qPilotPointSignedLogAtOne : Real :=
  I.sourceLocalLogDegree v
    (I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)))

/-- Actual equality: the q-pilot signed scalar at j=1 equals the signed local
log-volume of the q-pilot point, with the same card factor on both sides. -/
theorem qPilotSignedAtOne_eq_qPilotPointSignedLogAtOne
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    qPilotSignedAtOne I n = qPilotPointSignedLogAtOne I v R n := by
  unfold qPilotSignedAtOne qPilotPointSignedLogAtOne
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n
    (oneSignedLabel (l := l)) hdeg]
  rfl

/-- Projection formula for the actual point log-volume. -/
theorem qPilotPointSignedLogAtOne_eq_card_mul_log
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    qPilotPointSignedLogAtOne I v R n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0
          (oneSignedLabel (l := l))) :=
  I.sourceLocalLogDegree_thetaPilotPoint v R n
    (oneSignedLabel (l := l)) hdeg

end LeanFormal.IUT.Theorem311Source.OriginalInput.QPilotSignedJOneActual

end
