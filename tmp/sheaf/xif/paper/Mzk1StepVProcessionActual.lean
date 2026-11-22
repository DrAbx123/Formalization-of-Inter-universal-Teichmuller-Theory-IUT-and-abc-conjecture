import tmp.sheaf.xif.paper.S3014StepVProcessionAverageActual
import tmp.sheaf.xif.paper.S3029StepVAlignmentActual
import tmp.sheaf.xif.paper.S3050StepVQExpansionActual
import Mathlib.Tactic

/-!
# Mzk1StepVProcessionActual

Task-95: actual S3014ProcessionData candidate.

The actual per-label volume used here is the StepV scalar
  volume label := S3029StepVTerm places tuple istar jValue l label
which is the actual object built from stepVLambda and S3050Unit
(S3029StepVTerm = -stepVLambda * log p; S3050_stepVTerm_eq_label_sq_mul_unit).

The per-label comparison to S3014PerLabelBound reduces exactly to the
nonnegativity of the extra different/log p/exceptional term:
  S3014PerLabelBound - S3029StepVTerm
    = S3029DifferentTerm + log p + S3029ExceptionalTerm.

We construct S3014ProcessionData under this explicit extra-nonneg condition and
then apply S3014_processionAverage_of_data.  We do NOT assert the extra-nonneg
condition as proved; it is the exact remaining source/gap.  Also note that
S3029StepVTerm is the StepV bound scalar, not yet the normalized log-volume of
an actual region; the equality with arithmeticTupleNormalizedLogVolume of the
actual image region is a separate missing identification.

No sorry/axiom/True/PUnit/toy.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l n : Nat)

/-- The actual StepV per-label volume candidate. -/
noncomputable def stepVVolume (label : Nat) : Real :=
  S3029StepVTerm places tuple istar jValue l label

/-- Exact remaining extra term: different + log p + exceptional. -/
noncomputable def stepVExtraTerm : Real :=
  S3029DifferentTerm places tuple + Real.log (p : Real) +
    S3029ExceptionalTerm places tuple exceptional

/-- The explicit gap condition needed for the per-label bound. -/
def StepVExtraNonneg : Prop :=
  0 <= stepVExtraTerm (p := p) places tuple exceptional

/-- With the extra term nonnegative, the actual StepV volume is bounded by the
S3014 per-label bound. -/
theorem stepVVolume_le_perLabel (h : StepVExtraNonneg (p := p) places tuple exceptional)
    (label : Nat) :
    stepVVolume (p := p) places tuple istar jValue l label <=
      S3014PerLabelBound places tuple istar jValue exceptional l label := by
  have hdiff : S3014PerLabelBound places tuple istar jValue exceptional l label -
        stepVVolume (p := p) places tuple istar jValue l label =
      stepVExtraTerm (p := p) places tuple exceptional := by
    unfold S3014PerLabelBound stepVVolume S3029StepVTerm stepVExtraTerm
      S3029DifferentTerm S3029ExceptionalTerm
    ring
  have hh := h
  unfold StepVExtraNonneg at hh
  linarith

/-- Actual S3014ProcessionData with the StepV scalar, conditional on the
explicit extra-nonneg gap. -/
noncomputable def stepVProcessionData
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    S3014ProcessionData places tuple istar jValue exceptional l n where
  volume := stepVVolume (p := p) places tuple istar jValue l
  perLabel_bound := by
    intro label hlabel
    exact stepVVolume_le_perLabel (p := p) places tuple istar jValue exceptional l
      h label

/-- Consumer: the actual StepV average is bounded by the S3014 average bound,
conditional on the extra-nonneg gap. -/
theorem stepVProcessionAverage_bound
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    (1 / (n : Real)) *
        (∑ label ∈ Finset.Icc 1 n,
          stepVVolume (p := p) places tuple istar jValue l label) <=
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n :=
  S3014_processionAverage_of_data places tuple istar jValue exceptional l n
    (stepVProcessionData (p := p) places tuple istar jValue exceptional l n h)

#check stepVVolume
#check StepVExtraNonneg
#check stepVVolume_le_perLabel
#check stepVProcessionData
#check stepVProcessionAverage_bound

end LeanFormal.IUT.XiFPaper.Mzk1StepVProcessionActual

end
