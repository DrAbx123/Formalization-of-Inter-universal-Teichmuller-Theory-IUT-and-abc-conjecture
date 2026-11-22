import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBaseActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BaseProviderRestatedActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.RestatedLemma24InductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Rational24TargetBottomActual — BOTTOM LINE: rational 2.4 target (finite beta) UNCONDITIONAL

Lead A414: low-level wiring only.  Prerequisites verified green:
* B1: Mzk1BetaAvoidingFoldActual.betaAvoiding_all — Problem A fold, PROVED for all finite
  S subset Q and beta in Q outside S (EXIT0/SHA in coordinator records);
* B2: Mzk1BetaAvoidingBaseActual (EXIT0 10430B, src sha 691DFC7F...) — the PROVED fold
  theorem wired into the restated Lemma 2.4 base, including the spec repair: the named
  input BetaAvoidingBelyiBaseInput is FALSE at beta = infinity (polyEvalP1 q infinity =
  infinity in specialSet), so only the finite-beta form can be true.

DELIVERED HERE: the unconditional rational 2.4 target for finite beta, connected to the
specific interfaces RestatedLemma24InterfaceActual.Mzk1Lemma24Target and
Mzk1Lemma24BaseProviderRestatedActual (corrected finite-beta counterpart of its conditional
provider).  No high-level ABC/Cor312 wiring.  Scope: F=Q finite beta only; the full
P1(Qbar) reduction remains NAMED; NO closure claim; gate NOT PASSED; h22 binding HOLD.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Rational24TargetBottomActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBaseActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderRestatedActual

/-- **The bottom-line rational 2.4 target (finite beta)**: for every finite rational set S
and every rational b with ofFinite b outside S, the restated 2.4 target holds.
This is exactly B2's BetaAvoidingBelyiBaseInputCorrected. -/
def Rational24TargetFiniteBeta : Prop :=
  BetaAvoidingBelyiBaseInputCorrected

/-- **PROVED unconditionally** from B1 (fold) via B2. -/
theorem rational24TargetFiniteBeta_proved : Rational24TargetFiniteBeta :=
  betaAvoidingBelyiBaseInputCorrected_proved

/-- Pointwise target form (finite beta). -/
theorem Mzk1Lemma24Target_finite_beta_bottom (S : Finset (P1Point ℚ)) (b : ℚ)
    (hb : P1Point.ofFinite b ∉ S) : Mzk1Lemma24Target S (P1Point.ofFinite b) :=
  Mzk1Lemma24Target_finite_beta S b hb

/-- Corrected counterpart of Mzk1Lemma24BaseProviderRestatedActual's base provider:
the provider interface with the TRUE finite-beta premise. -/
def BaseProviderRestatedFinite : Prop :=
  Rational24TargetFiniteBeta

/-- The corrected base provider is PROVED. -/
theorem baseProviderRestatedFinite_proved : BaseProviderRestatedFinite :=
  rational24TargetFiniteBeta_proved

/-- Corrected provider theorem, same shape as
Mzk1Lemma24BaseProviderRestatedActual.mzk1Lemma24Target_of_betaAvoidingBelyiBase but with
the true finite-beta premise. -/
theorem mzk1Lemma24Target_of_betaAvoidingBelyiBaseCorrected
    (h : BetaAvoidingBelyiBaseInputCorrected) :
    ∀ (S : Finset (P1Point ℚ)) (b : ℚ),
      P1Point.ofFinite b ∉ S → Mzk1Lemma24Target S (P1Point.ofFinite b) :=
  h

/-- The old provider's premise is FALSE (spec repair; re-exported from B2): the old
conditional theorem cannot be instantiated and is not used. -/
theorem oldBaseProviderPremise_refuted : ¬ BetaAvoidingBelyiBaseInput :=
  not_betaAvoidingBelyiBaseInput

/-- The finite-beta restated base statement holds for every measure mu (B2 re-export). -/
theorem restatedBaseStatementFinite_bottom (μ : RestatedState → Nat × Nat) :
    RestatedBaseStatementFinite μ :=
  restatedBaseStatementFinite_proved μ

/-- The finite-beta restated induction conclusion (B2 re-export). -/
theorem restatedInductionConclusionFinite_bottom : RestatedInductionConclusionFinite :=
  restatedInductionConclusionFinite_proved

/-- Bottom rows: (component, evidence, status/scope). -/
def rational24BottomRows : List (String × String × String) :=
  [ ("B1 Problem A fold", "Mzk1BetaAvoidingFoldActual.betaAvoiding_all (PROVED all finite S, beta in Q)", "PREREQUISITE GREEN"),
    ("B2 corrected base", "Mzk1BetaAvoidingBaseActual.BetaAvoidingBelyiBaseInputCorrected / betaAvoidingBelyiBaseInputCorrected_proved", "PREREQUISITE GREEN"),
    ("spec repair (infinity beta)", "BetaAvoidingBelyiBaseInput FALSE at beta = infinity (B2 not_betaAvoidingBelyiBaseInput)", "RECORDED; old premise not used"),
    ("rational 2.4 target (finite beta)", "Rational24TargetFiniteBeta / rational24TargetFiniteBeta_proved / Mzk1Lemma24Target_finite_beta_bottom", "PROVED UNCONDITIONALLY"),
    ("restated 2.4 interface consumer", "RestatedLemma24InterfaceActual.Mzk1Lemma24Target", "CONNECTED"),
    ("base provider (corrected)", "BaseProviderRestatedFinite / baseProviderRestatedFinite_proved / mzk1Lemma24Target_of_betaAvoidingBelyiBaseCorrected", "PROVED (finite-beta counterpart of the conditional provider)"),
    ("restated induction base/conclusion (finite beta)", "restatedBaseStatementFinite_bottom / restatedInductionConclusionFinite_bottom", "RE-EXPORTED PROVED"),
    ("high-level wiring", "none (Lead A414: low-level line only; no ABC/Cor312 wiring)", "OUT OF SCOPE"),
    ("closure/status", "F=Q finite beta only; P1(Qbar) reduction NAMED; NO closure; gate NOT PASSED; h22 binding HOLD", "INTEGRITY") ]

theorem rational24BottomRows_length : rational24BottomRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Rational24TargetBottomActual

end
