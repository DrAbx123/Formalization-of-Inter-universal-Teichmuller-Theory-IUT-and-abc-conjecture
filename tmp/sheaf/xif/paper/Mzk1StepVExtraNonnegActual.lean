import tmp.sheaf.xif.paper.Mzk1StepVProcessionActual
import tmp.sheaf.xif.paper.S3029StepVAlignmentActual
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import Mathlib.Tactic

/-!
# Mzk1StepVExtraNonnegActual

Task-95/B6: actual nonnegativity of the StepV extra term.

The local different generator is integral and nonzero, so its normalized order
localNormOrder p (different) is nonnegative; the ramification exponent is
positive, so 3 + log(e) is nonnegative.  Hence
  S3029DifferentTerm + log p + S3029ExceptionalTerm >= 0,
which fills the explicit StepVExtraNonneg hypothesis of
Mzk1StepVProcessionActual.

No sorry/axiom/True/PUnit/toy.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVExtraNonnegActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVProcessionActual
open LeanFormal.IUT.LocalDifferentNormOrder
open LeanFormal.IUT.IntegralTraceDualTensorInclusion

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l n : Nat)

/-- The actual different generator has nonnegative normalized order. -/
theorem localNormOrder_arithmeticTupleLocalDifferent_nonneg (i : ι) :
    0 <= localNormOrder p (arithmeticTupleLocalDifferent places tuple i) := by
  change 0 <= localNormOrder p
    ((localDifferentGenerator (p := p)
      (L := CommonPrimeCompletion (places i (tuple i)))) :
        CommonPrimeCompletion (places i (tuple i)))
  rw [localNormOrder_differentGenerator_eq_paperOrder]
  unfold localDifferentPaperOrder
  apply div_nonneg
  · exact_mod_cast Nat.zero_le (localDifferentOrder (p := p)
      (L := CommonPrimeCompletion (places i (tuple i))))
  · exact_mod_cast (le_of_lt (logShellRamificationExponent_pos
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p)))

/-- The actual different term is nonnegative. -/
theorem S3029DifferentTerm_nonneg :
    0 <= S3029DifferentTerm places tuple := by
  unfold S3029DifferentTerm
  apply mul_nonneg
  · exact Finset.sum_nonneg (fun i _ =>
      localNormOrder_arithmeticTupleLocalDifferent_nonneg places tuple i)
  · exact Real.log_nonneg (by
      have hp1 : (1 : Real) <= (p : Real) := by
        exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le
      exact hp1)

/-- The actual exceptional term is nonnegative. -/
theorem S3029ExceptionalTerm_nonneg :
    0 <= S3029ExceptionalTerm places tuple exceptional := by
  unfold S3029ExceptionalTerm
  apply Finset.sum_nonneg
  intro i hi
  have hpos : 0 < logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) :=
    logShellRamificationExponent_pos (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  have hge : (1 : Real) <= (logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real) := by
    exact_mod_cast Nat.succ_le_of_lt hpos
  have hlog : 0 <= Real.log (logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real) :=
    Real.log_nonneg hge
  linarith

/-- The actual StepV extra term is nonnegative. -/
theorem stepVExtraNonneg_actual :
    StepVExtraNonneg (p := p) places tuple exceptional := by
  unfold StepVExtraNonneg stepVExtraTerm
  have hd := S3029DifferentTerm_nonneg (p := p) places tuple
  have he := S3029ExceptionalTerm_nonneg (p := p) places tuple exceptional
  have hp1 : (1 : Real) <= (p : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le
  have hl : 0 <= Real.log (p : Real) := Real.log_nonneg hp1
  linarith

/-- Unconditional actual StepV S3014 data. -/
noncomputable def stepVProcessionDataActual :
    S3014ProcessionData places tuple istar jValue exceptional l n :=
  stepVProcessionData (p := p) places tuple istar jValue exceptional l n
    (stepVExtraNonneg_actual (p := p) places tuple exceptional)

/-- Unconditional actual StepV average bound. -/
theorem stepVProcessionAverage_bound_actual :
    (1 / (n : Real)) *
        (∑ label ∈ Finset.Icc 1 n,
          stepVVolume (p := p) places tuple istar jValue l label) <=
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n :=
  S3014_processionAverage_of_data places tuple istar jValue exceptional l n
    (stepVProcessionDataActual (p := p) places tuple istar jValue exceptional l n)

#check localNormOrder_arithmeticTupleLocalDifferent_nonneg
#check S3029DifferentTerm_nonneg
#check S3029ExceptionalTerm_nonneg
#check stepVExtraNonneg_actual
#check stepVProcessionDataActual
#check stepVProcessionAverage_bound_actual

end LeanFormal.IUT.XiFPaper.Mzk1StepVExtraNonnegActual

end
