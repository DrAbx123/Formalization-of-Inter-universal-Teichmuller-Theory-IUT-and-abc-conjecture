import tmp.external.ported.flt.FLT.DedekindDomain.Completion.BaseChange
import tmp.sheaf.xif.paper.Mzk1P3AgreeDegreeActual
import tmp.sheaf.xif.paper.Mzk1P3BadCharTameDegreeActual
import Mathlib.Tactic

/-! # CONDITIONAL: FLT BaseChange comparison and degree multiplicativity

This file imports the ported FLT completion BaseChange file and records the two
local/global comparison theorems:
  ramificationIdx_eq_ramificationIdx
  inertiaDeg_eq_inertiaDeg
and the finrank multiplicativity theorem
  ramificationIdx_mul_inertiaDeg_eq_finrank.

It also formalizes the definitional identity
  relativeCompletionDegree = relativeResidueDegree * relativeRamificationIndex
(commuted form), and records the exact FLT input that upgrades it to
  relativeCompletionDegree = finrank of the completion extension.
No assertion that FLT applies to the actual IUT places is made here.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3AGREEFLTBridgeActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1P3BadCharTameDegreeActual

#check IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_eq_ramificationIdx
#check IsDedekindDomain.HeightOneSpectrum.adicCompletion.inertiaDeg_eq_inertiaDeg
#check IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- Commuted multiplicativity of the relative completion degree. -/
theorem relativeCompletionDegree_eq_residue_mul_ramification
    (place : NumberField.FinitePlace K) :
    relativeCompletionDegree (k := k) place =
      relativeResidueDegree (k := k) place *
        relativeRamificationIndex (k := k) place := by
  unfold relativeCompletionDegree
  exact Nat.mul_comm _ _

/-- Exact FLT input: the relative e*f equals the finrank of the completion
extension.  This is the form supplied by FLT's
ramificationIdx_mul_inertiaDeg_eq_finrank after comparing ramificationIdx' with
ramificationIdx and inertiaDeg' with inertiaDeg. -/
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

end LeanFormal.IUT.XiFPaper.Mzk1P3AGREEFLTBridgeActual
end
