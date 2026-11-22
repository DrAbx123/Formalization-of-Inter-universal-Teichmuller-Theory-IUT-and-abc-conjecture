import tmp.sheaf.xif.paper.Mzk1Thm25WiringActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StatementShapeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Thm25ConsumerActual — h22-discharge consumer for [Mzk1] Theorem 2.5 wiring

STEP 0 prior-art (reuse, no re-proof): Mzk1Thm25WiringActual (corrected;
Lemma22Hypotheses, Lemma22FullStatementShape, Lemma24Shape, thm25_of_22_24_and_geometricCore,
conclusion via PROVED mzk1Thm25Conclusion_of_geometricCore; CITABLE 10);
Mzk1Lemma22StatementShapeActual (stage4 Mzk1Lemma22FullShape definition +
fullShape_to_partial/fullShape_preserves; CITABLE); Mzk1Lemma22GChoiceConstructActual /
Mzk1Lemma22StepConstructionActual / Mzk1PolyChainRuleActual (stage4 chain: the named
hypothesis (i) will be proved there).  This file is the CONSUMER that discharges the
2.2 named hypothesis h22 in Mzk1Thm25WiringActual as soon as stage4 lands the
conditioned-∀ theorem, without editing the wiring file.

Paper: [Mzk1] Thm 2.5 statement lines 207-221 / proof 222-281; Lemma 2.2 lines
106-135; Lemma 2.4 lines 144-205.

HONEST SCOPE: wiring/consumer only; Thm 2.5 remains conditional on (i) the full 2.2
StatementShape proof (stage4), (ii) the Lemma 2.4 shape, (iii) the GeometricCore input.
No closure claim; registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25ConsumerActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual

universe u

/-- The remaining 2.2 gate in the exact form stage4 will prove: for every S, β
satisfying the paper Lemma 2.2 hypotheses, the full shape holds. -/
abbrev Lemma22FullShapeGate : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ),
    Lemma22Hypotheses S β → Mzk1Lemma22FullShape S β

/-- **h22 DISCHARGE:** given stage4's conditioned-∀ theorem (Lemma22FullShapeGate),
the Lemma 2.4 shape and the GeometricCore input, the [Mzk1] Thm 2.5 conclusion shape
follows.  This is Mzk1Thm25WiringActual.thm25_of_22_24_and_geometricCore with its
h22 named hypothesis discharged by the supplied gate theorem. -/
theorem thm25_of_full2_and_24 {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (hfull2 : Lemma22FullShapeGate) (h24 : Lemma24Shape.{u})
    (hcore : Mzk1GeometricCoreRecast c ε T D) :
    ∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W :=
  thm25_of_22_24_and_geometricCore c ε T D hfull2 h24 hcore

/-- The same discharge expressed only over the gate (no scheme data). -/
theorem lemma22FullStatementShape_of_gate (hfull2 : Lemma22FullShapeGate) :
    Lemma22FullStatementShape :=
  hfull2

/-- Consumer record: (component, evidence, status). -/
def mzk1Thm25ConsumerRows : List (String × String × String) :=
  [ ("(i) full Lemma 2.2 StatementShape (h22)", "Lemma22FullShapeGate := forall S beta, Lemma22Hypotheses S beta -> Mzk1Lemma22FullShape S beta; discharge lemma via lemma22FullStatementShape_of_gate (PROVED); gate itself is stage4's chain (Mzk1PolyChainRuleActual + Mzk1PolyUnramifiedCompositionActual + Mzk1Lemma22StepConstructionActual.lemma22StepExists_packaged + Mzk1GChoiceScaleActual.scaleOrdering_of_hypotheses/scale_realHypotheses_exists + Mzk1Lemma22GChoiceConstructActual)", "NAMED GATE (stage4 proving; consumer ready)"),
    ("(ii) Lemma 2.4 shape (h24)", "Mzk1Thm25WiringActual.Lemma24Shape (named hypothesis)", "NAMED HYPOTHESIS (2.4 F/D/M open)"),
    ("(iii) GeometricCore input", "Mzk1GeometricCoreRealStructureActual.Mzk1GeometricCoreRecast (real-structure skeleton)", "named hypothesis / class-D paper input"),
    ("Thm 2.5 conclusion step", "mzk1Thm25Conclusion_of_geometricCore (PROVED)", "PROVED (conditional on GeometricCore recast)"),
    ("paper-level Thm 2.5", "corpus statement 207-221 / proof 222-281", "NOT closed; wiring only (no closure claim)"),
    ("ScaleOrdering min extraction", "Mzk1GChoiceScaleActual.scaleOrdering / scale_orderings_exists_of_hypotheses (PROVED)", "PROVED (v4)"),
    ("ScaleRealHypotheses package", "Mzk1GChoiceScaleActual.scale_realHypotheses_exists (PROVED, v3)", "PROVED") ]

theorem mzk1Thm25ConsumerRows_length : mzk1Thm25ConsumerRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm25ConsumerActual

end
