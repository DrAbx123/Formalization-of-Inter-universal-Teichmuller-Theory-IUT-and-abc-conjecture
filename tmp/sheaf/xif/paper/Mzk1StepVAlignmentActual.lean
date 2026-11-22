import tmp.sheaf.xif.paper.S3029StepVAlignmentActual
import tmp.sheaf.xif.paper.S3050StepVQExpansionActual
import tmp.sheaf.xif.paper.Mzk1StepVProcessionActual
import Mathlib.Tactic

/-!
# Mzk1StepVAlignmentActual

Task-100: actual S3029AlignmentData instance.

Actual choices:
  D := S3029DifferentTerm places tuple
  Q := S3050Unit p jValue l                 (paper c_root unit)
  S := S3029ExceptionalTerm places tuple exceptional
  T := 0
  cD = 1, cQ = 0, cS = 0, cT = 0, c0 = 0
  sS = 1, sT = 0
  qCoeff label = label^2
  labelRest = 0

Then:
* DifferentTerm = cD*D + cQ*Q + cS*S + cT*T + c0;
* ExceptionalTerm = sS*S + sT*T;
* StepVTerm = label^2*Q = qCoeff label * Q + 0 (S3050_stepVTerm_eq_label_sq_mul_unit).

This is an actual alignment; it does NOT imply StepVExtraNonneg.  The latter is
definitionally 0 <= DifferentTerm + log p + ExceptionalTerm and still requires
actual nonnegativity of the different/exceptional terms.  No sorry/axiom.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVProcessionActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l n : Nat)

/-- Actual alignment with Q = S3050Unit (paper c_root unit). -/
noncomputable def actualAlignment :
    S3029AlignmentData places tuple istar jValue exceptional l
      (S3029DifferentTerm places tuple)
      (S3050Unit p jValue l)
      (S3029ExceptionalTerm places tuple exceptional) 0 where
  cD := 1
  cQ := 0
  cS := 0
  cT := 0
  c0 := 0
  sS := 1
  sT := 0
  qCoeff := fun label => (label : Real) ^ 2
  labelRest := fun _ => 0
  different_eq := by
    unfold S3029DifferentTerm
    ring
  exceptional_eq := by
    unfold S3029ExceptionalTerm
    ring
  stepV_eq := by
    intro label
    rw [S3050_stepVTerm_eq_label_sq_mul_unit]
    ring

/-- Actual StepV scalar equals qCoeff*Q for the actual alignment. -/
theorem actualStepVVolume_eq_alignment (label : Nat) :
    stepVVolume (p := p) places tuple istar jValue l label =
      (label : Real) ^ 2 * S3050Unit p jValue l := by
  unfold stepVVolume
  rw [S3050_stepVTerm_eq_label_sq_mul_unit]

/-- The S3029 affine consumer with the actual alignment. -/
theorem actual_perLabel_affine (label : Nat) :
    S3014PerLabelBound places tuple istar jValue exceptional l label =
      (actualAlignment (p := p) places tuple istar jValue exceptional l).cD *
          (S3029DifferentTerm places tuple) +
        ((actualAlignment (p := p) places tuple istar jValue exceptional l).qCoeff label +
          (actualAlignment (p := p) places tuple istar jValue exceptional l).cQ) *
          (S3050Unit p jValue l) +
        ((actualAlignment (p := p) places tuple istar jValue exceptional l).cS +
          (actualAlignment (p := p) places tuple istar jValue exceptional l).sS) *
          (S3029ExceptionalTerm places tuple exceptional) +
        ((actualAlignment (p := p) places tuple istar jValue exceptional l).cT +
          (actualAlignment (p := p) places tuple istar jValue exceptional l).sT) * 0 +
        ((actualAlignment (p := p) places tuple istar jValue exceptional l).c0 +
          Real.log (p : Real)) +
        (actualAlignment (p := p) places tuple istar jValue exceptional l).labelRest label :=
  S3029_perLabel_affine places tuple istar jValue exceptional l
    (S3029DifferentTerm places tuple)
    (S3050Unit p jValue l)
    (S3029ExceptionalTerm places tuple exceptional) 0
    (actualAlignment (p := p) places tuple istar jValue exceptional l) label

/-- StepVExtraNonneg is exactly nonnegativity of the actual extra term. -/
theorem stepVExtraNonneg_iff_actual :
    StepVExtraNonneg (p := p) places tuple exceptional <->
      0 <= S3029DifferentTerm places tuple + Real.log (p : Real) +
        S3029ExceptionalTerm places tuple exceptional := by
  unfold StepVExtraNonneg stepVExtraTerm
  rfl

/-- Actual alignment does not imply StepVExtraNonneg: the latter is equivalent
to the displayed sign condition (no proof of that sign is supplied here). -/
theorem stepVExtraNonneg_not_derived_from_alignment
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    0 <= S3029DifferentTerm places tuple + Real.log (p : Real) +
      S3029ExceptionalTerm places tuple exceptional :=
  (stepVExtraNonneg_iff_actual (p := p) places tuple exceptional).mp h

#check actualAlignment
#check actualStepVVolume_eq_alignment
#check actual_perLabel_affine
#check stepVExtraNonneg_iff_actual
#check stepVExtraNonneg_not_derived_from_alignment

end LeanFormal.IUT.XiFPaper.Mzk1StepVAlignmentActual

end
