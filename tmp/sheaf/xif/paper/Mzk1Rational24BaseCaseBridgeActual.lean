import tmp.sheaf.xif.paper.Mzk1Rational24TargetBottomActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionBaseCaseActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Rational24BaseCaseBridgeActual — B3 finite-beta 2.4 target ↔ Problem C BaseCaseProvider

Lead A417 (bottom line only; no high-level ABC/Cor312):
* B3 (stepxi): Mzk1Rational24TargetBottomActual — rational 2.4 target for FINITE beta is
  PROVED unconditionally from B1 fold via B2 (Rational24TargetFiniteBeta,
  Mzk1Lemma24Target_finite_beta_bottom).
* C (abc): Mzk1NestedInductionBaseCaseActual.baseCaseProvider_proved — the paper-scope
  BaseCaseProvider (all-rational states, P1(Qbar) including infinity) is PROVED
  unconditionally by the identity polynomial f = X and S_phi = rationalisation of S.
  It does NOT need the finite-beta fold base (different target: S_phi is an arbitrary
  rational set, not the fixed Belyi special set).

CONNECTION DELIVERED HERE:
1. The Problem C base case is discharged: re-export baseCaseProvider_proved and assemble
   paperScopeLemma24Statement_of_providers with it, so the ONLY remaining Problem C
   residual is the named StepProvider (P1 geometric map layer).
2. The two proved components are recorded as consistent: Rational24TargetFiniteBeta
   (B3, F=Q finite beta) and BaseCaseProvider (C, paper scope) both hold; they are
   separate layers, and the exact residual/scope split is recorded in rows.
No closure claims; gate NOT PASSED; h22 binding HOLD. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Rational24BaseCaseBridgeActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Rational24TargetBottomActual
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBaseCaseActual
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

/-- **Problem C base case discharged (re-export):** BaseCaseProvider is PROVED
unconditionally (abc identity-witness proof). -/
theorem baseCaseProvider_discharged : BaseCaseProvider :=
  baseCaseProvider_proved

/-- **Exact Problem C residual:** only the named StepProvider (P1 map layer) remains. -/
def ProblemCResidual : Prop := StepProvider

/-- **Problem C assembly with the PROVED base case:** from the single named residual
StepProvider, the paper-scope Lemma 2.4 statement follows. -/
theorem paperScopeLemma24Statement_of_provedBaseCase (hstep : ProblemCResidual) :
    PaperScopeLemma24Statement :=
  paperScopeLemma24Statement_of_providers baseCaseProvider_proved hstep

/-- **Consistency of B3 and C:** the finite-beta rational 2.4 target (B3) and the
paper-scope BaseCaseProvider (C) both hold; they are separate layers (B3's target fixes
the Belyi special set, C's S_phi is an arbitrary rational set). -/
theorem rational24_and_baseCase_proved :
    Rational24TargetFiniteBeta ∧ BaseCaseProvider :=
  ⟨rational24TargetFiniteBeta_proved, baseCaseProvider_proved⟩

/-- B3 finite-beta targets remain available pointwise (re-export). -/
theorem rational24Target_finite_beta_available (S : Finset (P1Point ℚ)) (b : ℚ)
    (hb : P1Point.ofFinite b ∉ S) :
    LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual.Mzk1Lemma24Target S
      (P1Point.ofFinite b) :=
  Mzk1Lemma24Target_finite_beta_bottom S b hb

/-- Bridge rows: (component, evidence, status/scope). -/
def rational24BaseCaseBridgeRows : List (String × String × String) :=
  [ ("B3 finite-beta rational 2.4 target", "Mzk1Rational24TargetBottomActual.Rational24TargetFiniteBeta / rational24TargetFiniteBeta_proved", "PROVED UNCONDITIONALLY (F=Q, finite beta; from B1 fold via B2)"),
    ("C paper-scope BaseCaseProvider", "Mzk1NestedInductionBaseCaseActual.baseCaseProvider_proved (identity f=X, S_phi = rationalisation of S)", "PROVED UNCONDITIONALLY (all-rational states; P1(Qbar) including infinity)"),
    ("layer relation", "B3 fixes the Belyi special set {inf,0,1}; C allows an arbitrary rational S_phi.  C does NOT need the finite-beta fold base; B3 is the F=Q finite-beta component.", "SEPARATE LAYERS; BOTH PROVED"),
    ("connection theorem", "baseCaseProvider_discharged + paperScopeLemma24Statement_of_provedBaseCase", "PROVED (base discharged; only StepProvider named)"),
    ("exact Problem C residual", "ProblemCResidual := StepProvider (P1 geometric map layer: f0 pole/infinity bookkeeping, CV containment, P1 morphism composition/transport)", "NAMED (single residual)"),
    ("consistency", "rational24_and_baseCase_proved : Rational24TargetFiniteBeta ∧ BaseCaseProvider", "PROVED"),
    ("high-level wiring", "none (A417 bottom line only; no ABC/Cor312)", "OUT OF SCOPE"),
    ("closure/status", "no closure; gate NOT PASSED; h22 binding HOLD; pins 14041", "INTEGRITY") ]

theorem rational24BaseCaseBridgeRows_length : rational24BaseCaseBridgeRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Rational24BaseCaseBridgeActual

end
