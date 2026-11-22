import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBaseActual

/-!
# Mzk1FixedBetaAssemblyActual — real assembly: fixed-beta choice from PROVED corrected base

Status: PENDING-VERIFY. No sorry, no axiom.
Consumer (not adapted copy): assembles the PROVED corrected finite-beta base and the
restated finite induction conclusion into the fixed-beta choice object, and records the
old (all-beta) input refutation alongside. Uses only proved theorems of
Mzk1BetaAvoidingBaseActual / Mzk1BetaAvoidingFoldActual. -/

noncomputable section

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderRestatedActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingFoldActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBaseActual

namespace LeanFormal.IUT.XiFPaper.Mzk1FixedBetaAssemblyActual

/-- The fixed-beta choice: corrected base + finite restatement of the induction conclusion. -/
structure FixedBetaChoice where
  base : BetaAvoidingBelyiBaseInputCorrected
  inductionConclusion : RestatedInductionConclusionFinite

/-- Genuine assembly theorem: the fixed-beta choice is inhabited (both fields PROVED). -/
theorem fixedBetaChoice_nonempty : Nonempty FixedBetaChoice :=
  ⟨{ base := betaAvoidingBelyiBaseInputCorrected_proved,
     inductionConclusion := restatedInductionConclusionFinite_proved }⟩

/-- Genuine assembly theorem: corrected base + pointwise finite-beta target. -/
theorem fixedBeta_corrected_base_and_pointwise :
    BetaAvoidingBelyiBaseInputCorrected ∧
      (∀ (S : Finset (P1Point ℚ)) (b : ℚ), P1Point.ofFinite b ∉ S →
        Mzk1Lemma24Target S (P1Point.ofFinite b)) :=
  ⟨betaAvoidingBelyiBaseInputCorrected_proved,
    fun S b hb => Mzk1Lemma24Target_finite_beta S b hb⟩

/-- Genuine assembly theorem: old all-beta input is false, corrected finite-beta input is true. -/
theorem fixedBeta_old_false_corrected_true :
    ¬ BetaAvoidingBelyiBaseInput ∧ BetaAvoidingBelyiBaseInputCorrected :=
  ⟨not_betaAvoidingBelyiBaseInput, betaAvoidingBelyiBaseInputCorrected_proved⟩

end LeanFormal.IUT.XiFPaper.Mzk1FixedBetaAssemblyActual
end
