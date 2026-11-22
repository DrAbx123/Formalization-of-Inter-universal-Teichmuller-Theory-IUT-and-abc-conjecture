import Mathlib
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionStepProviderActual
import LeanFormal.IUT.Audit.Status
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual

/-!
# Mzk1NestedInductionBetaTrackingActualAdapted (adapted copy, A475 reuse) — paper-shaped StepProvider (beta-tracking) assembly

STEP 0 prior-art: reuse Mzk1NestedInductionActual.induction_with_invariant (well-founded
(maxDegP,numMaxP) lex induction) and Mzk1NestedInductionStepProviderActual.stepTransport_of_goal
(target transport along beta' = f0 beta, PROVED conditional on CVCompositionLawF).
This file records the PAPER-SHAPED step provider: the step chooses S' (measure-decreasing)
independent of beta, and for every beta produces beta' with the backward transport
Target S' beta' -> Target S beta. The geometric construction of (S',beta') remains NAMED.
No closure claim; registry frozen 14041.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBetaTrackingActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

/-- Paper-shaped step provider (beta-tracking): S' is independent of beta; for each
beta notin S there is a transported parameter beta' avoiding S' and a backward target
transport. -/
def BetaTrackingStepProvider : Prop :=
  ∀ (S : Finset (P1Point (AlgebraicClosure ℚ))), 1 < maxDegP S →
    ∃ S' : Finset (P1Point (AlgebraicClosure ℚ)),
      Prod.Lex (· < ·) (· < ·) (maxDegP S', numMaxP S') (maxDegP S, numMaxP S) ∧
        ∀ (β : P1Point (AlgebraicClosure ℚ)), β ∉ S →
          ∃ β' : P1Point (AlgebraicClosure ℚ), β' ∉ S' ∧
            (PaperScopeLemma24Target S' β' → PaperScopeLemma24Target S β)

/-- Assembly with the paper-shaped provider: base provider (maxDegP ≤ 1) plus the
beta-tracking step provider give the paper-scope Lemma 2.4 statement by the proved
well-founded lexicographic induction (Goal is the ∀β statement). -/
theorem paperScopeLemma24Statement_of_betaTrackingProviders
    (hbase : ∀ (S : Finset (P1Point (AlgebraicClosure ℚ)))
      (β : P1Point (AlgebraicClosure ℚ)), β ∉ S → maxDegP S ≤ 1 →
        PaperScopeLemma24Target S β)
    (hstep : BetaTrackingStepProvider) : PaperScopeLemma24Statement := by
  intro S β hβ
  let Goal : Finset (P1Point (AlgebraicClosure ℚ)) → Prop :=
    fun S => ∀ β : P1Point (AlgebraicClosure ℚ), β ∉ S → PaperScopeLemma24Target S β
  have hmain : ∀ S : Finset (P1Point (AlgebraicClosure ℚ)), Goal S := by
    refine induction_with_invariant
      (μ := fun S : Finset (P1Point (AlgebraicClosure ℚ)) => (maxDegP S, numMaxP S))
      (Inv := fun _ => True) (Goal := Goal) ?_ ?_
    · intro s _ hsmall β hβ'
      exact hbase s β hβ' hsmall
    · intro s _ hbig
      obtain ⟨S', hlex, htrans⟩ := hstep s hbig
      refine ⟨S', trivial, hlex, ?_⟩
      intro hG β' hβ'
      obtain ⟨β'', hβ'', htr⟩ := htrans β' hβ'
      exact htr (hG β'' hβ'')
  exact hmain S β hβ

/-- Row record: what is proved vs the named geometric construction. -/
def betaTrackingRows : List (String × String × String) :=
  [ ("paper-shaped beta-tracking step provider", "DEFINED", "BetaTrackingStepProvider (S' independent of beta; beta' with transport)")
  , ("base provider (maxDegP ≤ 1)", "HYPOTHESIS (same-beta form PROVED via baseCaseProvider_proved)", "hbase argument")
  , ("beta-tracking assembly", "PROVED (conditional on the two providers)", "paperScopeLemma24Statement_of_betaTrackingProviders")
  , ("geometric construction of (S', beta')", "NAMED", "normalised f0 + analytic avoidance; not formalized")
  , ("relation to same-beta StepProvider", "NOTE", "StepProvider (Mzk1NestedInductionActual) is the same-beta plumbing; this records the paper-shaped form used by stepTransport_of_goal") ]

theorem betaTrackingRows_length : betaTrackingRows.length = 5 := rfl

#check BetaTrackingStepProvider
#check paperScopeLemma24Statement_of_betaTrackingProviders
#check betaTrackingRows_length

end LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBetaTrackingActualAdapted
end
