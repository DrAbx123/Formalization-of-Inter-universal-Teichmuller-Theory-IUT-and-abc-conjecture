/- O6 P3: termination of the general branch-pinning recursion (route §4.3): the lexicographic
measure `(max degree, count at max degree)` is well-founded, so the Belyi degree reduction
(`Mzk1G1O6M2PinStepActual.pinReductionStep_holds`) can be iterated to a normal form.
REUSE: `Mzk1G1O6M2PinGeneralActual.pinLt` / `Mzk1G1O6M2PinStepActual.pinReductionStep_holds`
(this lane), `WellFounded.prod_lex` / `InvImage.wf` / `Subrelation.wf` (Mathlib).
The reverse-composition step (assembling the final polynomial from the reduction chain) is
the next batch; the finite-beta base case is `Mzk1Consumer24AdapterUnconditionalActual`
`finiteBetaCorrectedBase_proved` (donor, not imported here yet). -/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinStepActual
import Mathlib.Order.RelClasses
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinComposeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinStepActual

/-- The lexicographic measure as a pair of naturals. -/
def pinMeasure (P : Finset ℚ[X]) : ℕ × ℕ :=
  (pinMaxDeg P, pinCountMax P)

/-- The lexicographic relation on finite sets, expressed through the measure. -/
def pinLex (A B : Finset ℚ[X]) : Prop :=
  Prod.Lex (· < ·) (· < ·) (pinMeasure A) (pinMeasure B)

/-- `pinLt` is exactly the lexicographic comparison of the measures. -/
theorem pinLt_iff_pinLex (A B : Finset ℚ[X]) : pinLt A B ↔ pinLex A B := by
  unfold pinLex pinLt pinMeasure
  rw [Prod.lex_iff]

theorem wellFounded_pinLex : WellFounded pinLex :=
  InvImage.wf pinMeasure (WellFounded.prod_lex wellFounded_lt wellFounded_lt)

/-- **Termination of the pinning recursion**: the lexicographic order on finite sets of
polynomials is well-founded. -/
theorem wellFounded_pinLt : WellFounded pinLt := by
  refine Subrelation.wf ?_ wellFounded_pinLex
  intro A B h
  exact (pinLt_iff_pinLex A B).mp h

#print axioms pinLt_iff_pinLex
#print axioms wellFounded_pinLex
#print axioms wellFounded_pinLt
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinComposeActual