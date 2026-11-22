import tmp.sheaf.xif.paper.Mzk1P3AgreeDegreeActual
import Mathlib.Tactic

/-! # GREEN: FLT finrank input interface and degree multiplicativity -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3FLTCompletionInputActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- Commuted multiplicativity of the relative completion degree. -/
theorem relativeCompletionDegree_eq_residue_mul_ramification
    (place : NumberField.FinitePlace K) :
    relativeCompletionDegree (k := k) place =
      relativeResidueDegree (k := k) place *
        relativeRamificationIndex (k := k) place := by
  unfold relativeCompletionDegree
  exact Nat.mul_comm _ _

/-- Exact FLT input: relative e*f equals the finrank of the completion extension.
FLT's ramificationIdx_mul_inertiaDeg_eq_finrank supplies the global e*f = finrank;
the ramificationIdx'/ramificationIdx and inertiaDeg'/inertiaDeg comparisons identify
the global factors with the relative ones. -/
def FLTCompletionFinrankInput (place : NumberField.FinitePlace K) : Prop :=
  relativeRamificationIndex (k := k) place * relativeResidueDegree (k := k) place =
    Module.finrank
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K)

/-- Under the FLT finrank input, relativeCompletionDegree is the finrank. -/
theorem relativeCompletionDegree_eq_finrank_of_FLT
    (place : NumberField.FinitePlace K)
    (h : FLTCompletionFinrankInput (k := k) place) :
    relativeCompletionDegree (k := k) place =
      Module.finrank
        ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) := by
  unfold relativeCompletionDegree
  exact h

#check relativeCompletionDegree_eq_residue_mul_ramification
#check FLTCompletionFinrankInput
#check relativeCompletionDegree_eq_finrank_of_FLT
end LeanFormal.IUT.XiFPaper.Mzk1P3FLTCompletionInputActual
end
