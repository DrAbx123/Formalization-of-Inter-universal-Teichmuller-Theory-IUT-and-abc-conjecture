import tmp.sheaf.xif.paper.QPilotSignedJOneActual

/-! # q-pilot card factor at j = 1

The source q-side signed value at j = 1 is

  sourceQSideNormalizedValue I n oneSignedLabel
    = card(SourceVolumeIndex l) * log (thetaValueAt n 0 oneSignedLabel).

The same card(SourceVolumeIndex) factor appears in the signed local log-volume
of the actual q-pilot point:

  sourceLocalLogDegree v (sourceThetaPilotPoint v R n oneSignedLabel)
    = card(SourceVolumeIndex l) * log (thetaValueAt n 0 oneSignedLabel).

This file constructs both the normalized scalar (log q_v) and the card-scaled
q-pilot signed scalar, proves their exact card relation, and proves the
card-scaled scalar equals the signed local hull-generator value at j = 1.

The full hull supremum is not identified with the single j = 1 point value;
that is a separate maximality statement and is not assumed here.  No fake
equality or inequality.  No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.OriginalInput.QPilotCardFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.Theorem311Source.OriginalInput.QPilotSignedJOneActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)

/-- The normalized q-pilot signed scalar at j=1: log of the actual theta value,
without the SourceVolumeIndex cardinality factor. -/
noncomputable def normalizedQPilotSignedAtOne : Real :=
  Real.log (I.thetaValueAt (n.val : Int) 0 (oneSignedLabel (l := l)))

/-- The card-scaled q-pilot signed scalar at j=1:
card(SourceVolumeIndex) * normalizedQPilotSignedAtOne. -/
noncomputable def cardQPilotSignedAtOne : Real :=
  (Fintype.card (SourceVolumeIndex l) : Real) *
    normalizedQPilotSignedAtOne I n

/-- The card-scaled scalar is exactly the source q-side normalized value. -/
theorem cardQPilotSignedAtOne_eq_sourceQSide :
    cardQPilotSignedAtOne I n =
      I.sourceQSideNormalizedValue n (oneSignedLabel (l := l)) := rfl

/-- Exact card relation: card-scaled = card * normalized. -/
theorem cardQPilotSignedAtOne_eq_card_mul_normalized :
    cardQPilotSignedAtOne I n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        normalizedQPilotSignedAtOne I n := rfl

/-- The signed local log-volume of the actual q-pilot point at j=1, i.e. the
signed hull-generator value at j=1. -/
noncomputable def signedHullGeneratorValueAtOne : Real :=
  I.sourceLocalLogDegree v
    (I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)))

/-- Actual equality with the same card factor: the card-scaled q-pilot scalar
equals the signed hull-generator value at j=1. -/
theorem cardQPilotSignedAtOne_eq_signedHullGeneratorValue
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    cardQPilotSignedAtOne I n = signedHullGeneratorValueAtOne I v R n := by
  unfold cardQPilotSignedAtOne normalizedQPilotSignedAtOne
    signedHullGeneratorValueAtOne
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n
    (oneSignedLabel (l := l)) hdeg]
  rfl

/-- The signed hull-generator value is card times the normalized scalar. -/
theorem signedHullGeneratorValueAtOne_eq_card_mul_normalized
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    signedHullGeneratorValueAtOne I v R n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        normalizedQPilotSignedAtOne I n :=
  (cardQPilotSignedAtOne_eq_signedHullGeneratorValue I v R n hdeg).symm.trans
    (cardQPilotSignedAtOne_eq_card_mul_normalized I n)

/-- Since the card factor is nonzero, the normalized scalar is the divided
signed hull-generator value. -/
theorem normalizedQPilotSignedAtOne_eq_signedHullGeneratorValue_div_card
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    normalizedQPilotSignedAtOne I n =
      signedHullGeneratorValueAtOne I v R n /
        (Fintype.card (SourceVolumeIndex l) : Real) := by
  have hcard_nat : 0 < Fintype.card (SourceVolumeIndex l) :=
    sourceVolumeIndex_card_pos l
  have hcard : (Fintype.card (SourceVolumeIndex l) : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcard_nat)
  rw [signedHullGeneratorValueAtOne_eq_card_mul_normalized I v R n hdeg]
  field_simp [hcard]

end LeanFormal.IUT.Theorem311Source.OriginalInput.QPilotCardFactorActual

end
