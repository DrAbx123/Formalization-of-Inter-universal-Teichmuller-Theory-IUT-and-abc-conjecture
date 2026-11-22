import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison

/-!
# Corrected positive source log-volume

The old SourceImageHullVolume.sourcePointVolume is

  ENNReal.ofReal (sourceLocalLogDegree v x).

For a theta-pilot point, sourceLocalLogDegree is

  card(SourceVolumeIndex l) * Real.log (thetaValueAt n 0 j),

which is negative because thetaValueAt < 1.  ENNReal.ofReal truncates it to
zero.  This file constructs the corrected positive log-volume

  positivePointLogVolume v x := -sourceLocalLogDegree v x,

proves the actual theta-pilot formula and positivity under thetaValueAt < 1, and
records the old truncated value as exactly zero.

This is a sign correction.  It does not assert any xi-f inequality.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.OriginalInput.SourceHullVolumeSignCorrectedActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)

/-- Corrected positive point log-volume: the negative of the signed
log-degree. -/
noncomputable def positivePointLogVolume (x : I.ThetaPilotPoint v) : Real :=
  -I.sourceLocalLogDegree v x

/-- Corrected positive set log-volume: the supremum of the positive point
log-volumes over the set. -/
noncomputable def positiveSetLogVolume (S : Set (I.ThetaPilotPoint v)) : ENNReal :=
  ⨆ x ∈ S, ENNReal.ofReal (positivePointLogVolume (I := I) v x)

/-- Corrected positive hull log-volume: the positive set log-volume of the
actual source holomorphic hull. -/
noncomputable def positiveHullLogVolume (n : ThetaPilotCarrier l) : ENNReal :=
  positiveSetLogVolume (I := I) v
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))

/-- Actual theta-pilot point formula for the corrected positive log-volume. -/
theorem positivePointLogVolume_thetaPilotPoint
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    positivePointLogVolume (I := I) v
        (I.sourceThetaPilotPoint v R n j) =
      -((Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j)) := by
  unfold positivePointLogVolume
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n j hdeg]

/-- The corrected positive theta-pilot log-volume is positive under the actual
theta contraction thetaValueAt < 1. -/
theorem positivePointLogVolume_thetaPilotPoint_pos
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hθ : I.thetaValueAt (n.val : Int) 0 j < 1) :
    0 < positivePointLogVolume (I := I) v
        (I.sourceThetaPilotPoint v R n j) := by
  rw [positivePointLogVolume_thetaPilotPoint (I := I) v R n j hdeg]
  have hlog : Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 :=
    Real.log_neg (I.thetaValueAt_pos (n.val) 0 j) hθ
  have hcard_nat : 0 < Fintype.card (SourceVolumeIndex l) :=
    sourceVolumeIndex_card_pos l
  have hcard : (0 : Real) < (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast hcard_nat
  have hprod : (Fintype.card (SourceVolumeIndex l) : Real) *
      Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 :=
    mul_neg_of_pos_of_neg hcard hlog
  linarith

/-- The old sourcePointVolume at the same theta-pilot point is exactly zero:
this is the ENNReal truncation fact. -/
theorem oldSourcePointVolume_thetaPilotPoint_eq_zero
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hθ : I.thetaValueAt (n.val : Int) 0 j < 1) :
    I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j) = 0 := by
  rw [I.sourcePointVolume_thetaPilotPoint v R n j hdeg]
  apply ENNReal.ofReal_of_nonpos
  have hlog : Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 :=
    Real.log_neg (I.thetaValueAt_pos (n.val) 0 j) hθ
  have hcard_nat : 0 < Fintype.card (SourceVolumeIndex l) :=
    sourceVolumeIndex_card_pos l
  have hcard : (0 : Real) < (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast hcard_nat
  exact le_of_lt (mul_neg_of_pos_of_neg hcard hlog)

/-- The corrected positive theta-pilot value is the negative of the actual
signed value sourceQSideNormalizedValue. -/
theorem positivePointLogVolume_thetaPilotPoint_eq_neg_sourceQSide
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    positivePointLogVolume (I := I) v
        (I.sourceThetaPilotPoint v R n j) =
      -I.sourceQSideNormalizedValue n j := by
  rw [positivePointLogVolume_thetaPilotPoint (I := I) v R n j hdeg]
  rfl

/-- The actual positive hull log-volume is the corrected object; it is defined
from the true positive point log-volume, not from ENNReal.ofReal of a negative
log-degree. -/
theorem positiveHullLogVolume_eq (n : ThetaPilotCarrier l) :
    positiveHullLogVolume (I := I) v R n =
      ⨆ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        ENNReal.ofReal (positivePointLogVolume (I := I) v x) :=
  rfl

end LeanFormal.IUT.Theorem311Source.OriginalInput.SourceHullVolumeSignCorrectedActual

end
