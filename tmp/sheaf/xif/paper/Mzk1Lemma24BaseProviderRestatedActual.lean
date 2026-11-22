import Mathlib
import tmp.sheaf.xif.paper.RestatedLemma24InductionActual
import tmp.sheaf.xif.paper.PaperScopeLemma24Actual
import tmp.sheaf.xif.paper.Mzk1Lemma24ProofActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderRestatedActual

open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- **Conditional base provider** (Lead A313/A314): the named class-B beta-avoiding
Belyi input directly yields the restated 2.4 target for every rational state with beta
outside S.  This is a CONSEQUENCE of the named input; it does not prove the input. -/
theorem s3135_target_of_betaAvoidingBelyiBase
    (h : BetaAvoidingBelyiBaseInput) :
    ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), β ∉ S → Mzk1Lemma24Target S β :=
  h

/-- **Conditional assembly chain** (Lead A313/A314): given the named beta-avoiding Belyi
base input, the named step provider for a fixed measure mu with well-founded lexicographic
value, the restated induction conclusion follows by well-founded recursion (the base is
the F = Q component; the step provider is the named paper 163-206 input).  CONDITIONAL on
named class-B inputs; no closure claimed. -/
theorem s3135_restatedConclusion_of_providers
    (hbase : BetaAvoidingBelyiBaseInput)
    (μ : RestatedState → Nat × Nat)
    (hwf : WellFounded (fun a b : RestatedState => lemma24Measure (μ a) (μ b)))
    (hstep : CorrectedStepProviderPaperInput μ) :
    RestatedInductionConclusion := by
  intro st hβ
  let r : RestatedState → RestatedState → Prop := fun a b => lemma24Measure (μ a) (μ b)
  have hmain : ∀ x : RestatedState, x.2 ∉ x.1 → Mzk1Lemma24Target x.1 x.2 := by
    refine hwf.fix ?_
    intro x rec hx
    by_cases h0 : μ x = (0, 0)
    · exact hbase x.1 x.2 hx
    · obtain ⟨step⟩ := hstep x h0 hx
      exact step.transport (rec step.next step.decrease step.next_beta_avoid)
  exact hmain st hβ

/-- Status: conditional base provider + conditional assembly chain filed.  These theorems
are conditional on the named class-B inputs (BetaAvoidingBelyiBaseInput,
CorrectedStepProviderPaperInput); the paper-scope algebraic layer remains named
(AlgebraicNestedInductionInput).  No closure claim; binding HOLD; registry frozen 14041. -/
def BaseProviderRestatedStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.base-provider-restated"
    source := "Lead A313/A314 scope decision; papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4"
    status := Audit.VerificationStatus.interface
    note := "PROVED (conditional): s3135_target_of_betaAvoidingBelyiBase (BetaAvoidingBelyiBaseInput => target for rational states) and s3135_restatedConclusion_of_providers (base + fixed-mu well-founded step provider => RestatedInductionConclusion by well-founded recursion; step carries next_beta_avoid so beta-outside invariant is preserved). CONDITIONAL on named class-B inputs; F = Q component only; paper-scope algebraic layer named AlgebraicNestedInductionInput; no closure claim; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.rational-input-scope", "MZK1.lemma24.paper-scope" ]
    sorryItems :=
      [ "BetaAvoidingBelyiBaseInput (class-B named; conditional theorems consume it)",
        "CorrectedStepProviderPaperInput (class-B named)",
        "AlgebraicNestedInductionInput (paper-scope algebraic layer, class-B named)" ] }


/-- Lead-named alias (A318): conditional base provider. -/
theorem mzk1Lemma24Target_of_betaAvoidingBelyiBase
    (h : BetaAvoidingBelyiBaseInput) :
    ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), β ∉ S → Mzk1Lemma24Target S β :=
  s3135_target_of_betaAvoidingBelyiBase h

/-- Lead-named conditional assembly chain (A318): given the named beta-avoiding Belyi base
input, the named assembly statement (RestatedInductionAssemblyStatement as a named
hypothesis) and the named step provider, the restated induction conclusion follows.  All
heavy inputs remain named; no closure claim. -/
theorem mzk1Lemma24Target_of_assembly
    (hbase : BetaAvoidingBelyiBaseInput)
    (μ : RestatedState → Nat × Nat)
    (hassembly : CorrectedAssemblyPaperInput μ)
    (hstep : CorrectedStepProviderPaperInput μ) :
    RestatedInductionConclusion :=
  hassembly (fun st _ hβ => hbase st.1 st.2 hβ) hstep

#check mzk1Lemma24Target_of_assembly
#check s3135_target_of_betaAvoidingBelyiBase
#check s3135_restatedConclusion_of_providers
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderRestatedActual
end-- base-provider-revive-bump