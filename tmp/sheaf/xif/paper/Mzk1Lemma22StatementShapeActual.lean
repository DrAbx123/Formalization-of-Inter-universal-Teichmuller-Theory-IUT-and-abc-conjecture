import tmp.sheaf.xif.paper.Mzk1PolyUnramifiedCompositionActual
import tmp.sheaf.xif.paper.Mzk1Lemma22InductionActual
import Mathlib.Tactic

/-! # Mzk1Lemma22StatementShapeActual — full Lemma 2.2 StatementShape (polynomial level, unramifiedness included)

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135; Mzk1PolyMapActual (polyMapPoints,
specialSet, polyUnramifiedAt), Mzk1PolyChainRuleActual (chain rule PROVED),
Mzk1PolyUnramifiedCompositionActual (unramifiedness composes for polynomial maps),
Mzk1Lemma22CompositionActual / Mzk1Lemma22InductionActual (partial shape + strong
induction), Mzk1Lemma22StepConstructionActual (stepxi; card collapse + steps).

PAPER: there exists nonconstant f in Q[x] with phi(S) subset {0,1,infinity},
phi(beta) notin {0,1,infinity}, and phi unramified over P^1 minus {0,1,infinity}.

THIS FILE defines the full polynomial-level shape used by the Thm 2.5 wiring:
Mzk1Lemma22FullShape S beta := exists f with 1 <= f.natDegree,
polyMorphism f preserves S into specialSet, avoids beta, and is unramified over the
complement of specialSet with predicate polyUnramifiedAt f.  It also proves the
projections and the implication to the interface-level partial shape. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionActual

/-- Polynomial-level full Lemma 2.2 shape for the target set {0,1,infinity}. -/
def Mzk1Lemma22FullShape (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  ∃ (f : ℚ[X]) (hdeg : 1 ≤ f.natDegree),
    PreservesSet (polyMorphism f hdeg) (↑S : Set (P1Point ℚ)) specialSet ∧
    AvoidsPoint (polyMorphism f hdeg) β specialSet ∧
    UnramifiedOver (polyMorphism f hdeg) {p | p ∉ specialSet} (polyUnramifiedAt f)

/-- Full shape gives the interface-level partial shape (via the same polynomial map). -/
theorem fullShape_to_partial (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (h : Mzk1Lemma22FullShape S β) :
    Mzk1Lemma22PartialShape (K := ℚ) S β 2 specialSet := by
  obtain ⟨f, hdeg, hpres, hav, _hunr⟩ := h
  exact ⟨polyMorphism f hdeg, hdeg, hpres, hav⟩

/-- Projections of the full shape. -/
theorem fullShape_preserves {S : Finset (P1Point ℚ)} {β : P1Point ℚ}
    (h : Mzk1Lemma22FullShape S β) :
    ∃ (f : ℚ[X]) (hdeg : 1 ≤ f.natDegree),
      PreservesSet (polyMorphism f hdeg) (↑S : Set (P1Point ℚ)) specialSet ∧
      AvoidsPoint (polyMorphism f hdeg) β specialSet ∧
      UnramifiedOver (polyMorphism f hdeg) {p | p ∉ specialSet} (polyUnramifiedAt f) := h

/-- The full shape is target-{0,1,infinity}-specific; record its corpus row. -/
structure Mzk1Lemma22FullShapeRow where
  item : String
  status : String
  proved : Bool

def mzk1Lemma22FullShapeRows : List Mzk1Lemma22FullShapeRow :=
  [ ⟨"full polynomial-level shape with unramifiedness", "DEFINITION (this file)", true⟩,
    ⟨"full shape => interface partial shape", "PROVED (fullShape_to_partial)", true⟩,
    ⟨"chain-rule composition of unramifiedness", "PROVED (Mzk1PolyChainRuleActual + Mzk1PolyUnramifiedCompositionActual)", true⟩,
    ⟨"assembly: step construction + induction + chain rule => full shape", "PENDING (next batch; consumes stepxi Mzk1Lemma22StepConstructionActual)", false⟩ ]

theorem mzk1Lemma22FullShapeRows_length : mzk1Lemma22FullShapeRows.length = 4 := rfl

#check Mzk1Lemma22FullShape
#check fullShape_to_partial
#check fullShape_preserves
#check mzk1Lemma22FullShapeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual
end
