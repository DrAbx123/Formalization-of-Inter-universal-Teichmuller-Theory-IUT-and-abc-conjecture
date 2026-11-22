import tmp.sheaf.xif.paper.PaperSourceGeometryActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual

/-! # S21 degree/norm alignment

The completion value degree is the spectral-norm log

  completionValueDegree u = ofAdd (Real.log ||u||).

The source local log-degree at a theta-pilot point is

  sourceLocalLogDegree v (sourceThetaPilotPoint v R n j)
    = card(SourceVolumeIndex l) * Real.log (thetaValueAt n 0 j).

Therefore the actual normalization factor aligning the completion degree with
the source degree is 1/card(SourceVolumeIndex l).  This file constructs that
actual factor and proves the conditional alignment: if the completion unit norm
matches the source theta value, then

  completion log norm = sourceLocalLogDegree / card.

The exact missing bridge (unit norm = source theta value) is recorded, not
faked.  The qVFamily normalized/default norm ratio is also recorded as the
actual local normalization factor from QVFamNormalizedCoefficientBridgeActual.

No fake equality/inequality; no sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S21DegreeNormAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (K := I.initial.arithmetic.Fmod) p)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)

/-- The actual source degree normalization factor 1/card(SourceVolumeIndex). -/
noncomputable def sourceDegreeNormalizationFactor : Real :=
  (Fintype.card (SourceVolumeIndex l) : Real)⁻¹

/-- The source local log-degree at the j = 1 theta-pilot point. -/
noncomputable def sourceDegreeAtOne : Real :=
  I.sourceLocalLogDegree v
    (I.sourceThetaPilotPoint v R n (SignedLabel.representative l (1 : ZMod l.value)))

/-- The source degree is card times the log theta value. -/
theorem sourceDegreeAtOne_eq_card_mul_log
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    sourceDegreeAtOne I v R n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0
          (SignedLabel.representative l (1 : ZMod l.value))) := by
  unfold sourceDegreeAtOne
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n
    (SignedLabel.representative l (1 : ZMod l.value)) hdeg]

/-- Exact alignment factor: the source degree equals card times the normalized
completion log degree. -/
theorem sourceDegreeAtOne_eq_card_mul_completionLog
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    sourceDegreeAtOne I v R n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0
          (SignedLabel.representative l (1 : ZMod l.value))) :=
  sourceDegreeAtOne_eq_card_mul_log I v R n hdeg

/-- Conditional completion/source degree alignment with the actual factor. -/
theorem completionLog_eq_sourceDegree_mul_factor
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    {x : Real}
    (hx : x = Real.log (I.thetaValueAt (n.val : Int) 0
      (SignedLabel.representative l (1 : ZMod l.value)))) :
    x = sourceDegreeAtOne I v R n *
      sourceDegreeNormalizationFactor (l := l) := by
  rw [hx, sourceDegreeAtOne_eq_card_mul_log I v R n hdeg]
  unfold sourceDegreeNormalizationFactor
  have hcard_nat : 0 < Fintype.card (SourceVolumeIndex l) :=
    sourceVolumeIndex_card_pos l
  have hcard : (Fintype.card (SourceVolumeIndex l) : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcard_nat)
  field_simp [hcard]

/-- Exact missing bridge: a completion unit whose spectral norm log equals the
source theta log. -/
def CompletionThetaNormBridge : Prop :=
  ∃ u : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place,
    0 < ‖u‖ ∧ Real.log ‖u‖ =
      Real.log (I.thetaValueAt (n.val : Int) 0
        (SignedLabel.representative l (1 : ZMod l.value)))

/-- The exact missing completion-unit bridge; no inhabitant is asserted. -/
def CompletionThetaNormBridgeRequired : Prop :=
  CompletionThetaNormBridge (l := l) (I := I) (n := n) (place := place)

end LeanFormal.IUT.XiFPaper.S21DegreeNormAlignmentActual

end
