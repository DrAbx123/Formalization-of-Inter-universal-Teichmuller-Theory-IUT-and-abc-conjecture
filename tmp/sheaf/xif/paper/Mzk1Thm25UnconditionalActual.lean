import tmp.sheaf.xif.paper.Mzk1Thm25ConsumerActual
import tmp.sheaf.xif.paper.Mzk1Lemma22ConditionedActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Thm25UnconditionalActual — [Mzk1] Theorem 2.5 UNCONDITIONAL conclusion (h22 discharged)

STEP 0 prior-art (reuse, no re-proof): Mzk1Thm25WiringActual (corrected, paper-conditioned
h22 chain; CITABLE 10); Mzk1Thm25ConsumerActual (Lemma22FullShapeGate and
thm25_of_full2_and_24; CITABLE 5); stage4 Mzk1Lemma22ConditionedActual
(mzk1Lemma22_fullShape_gate : ∀ S β, Lemma22Hypotheses S β → Mzk1Lemma22FullShape S β —
the FULL Lemma 2.2 StatementShape, from the conditioned induction with H-preservation).
This file is the ONE-LINE h22 binding: the named 2.2 hypothesis of the wiring is
discharged by stage4's proved gate, so the [Mzk1] Thm 2.5 conclusion holds with no
2.2 hypothesis — unconditionally modulo the Lemma 2.4 shape and the GeometricCore
(real-structure) input.

HONEST SCOPE: (i) full Lemma 2.2 is now PROVED (stage4); (ii) Lemma 2.4 shape remains a
named hypothesis; (iii) GeometricCore remains a named hypothesis; the paper-level
Theorem 2.5 is conditional only on (ii)+(iii). No closure claim beyond that.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25UnconditionalActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ConditionedActual

universe u

/-- The full Lemma 2.2 StatementShape is UNCONDITIONAL (stage4's proved gate). -/
theorem lemma22FullStatementShape_unconditional :
    Lemma22FullStatementShape :=
  mzk1Lemma22_fullShape_gate

/-- **[Mzk1] Theorem 2.5 conclusion, h22 DISCHARGED:** given the Lemma 2.4 shape and
the GeometricCore (real-structure) input, the Thm 2.5 conclusion follows with the
full Lemma 2.2 supplied by stage4's proved gate (no 2.2 hypothesis remains). -/
theorem thm25_of_lemma24_and_geometricCore {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (h24 : Lemma24Shape.{u}) (hcore : Mzk1GeometricCoreRecast c ε T D) :
    ∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W :=
  thm25_of_full2_and_24 c ε T D mzk1Lemma22_fullShape_gate h24 hcore

/-- Rows: (component, evidence, status). -/
def mzk1Thm25UnconditionalRows : List (String × String × String) :=
  [ ("full Lemma 2.2 (h22) discharged", "stage4 Mzk1Lemma22ConditionedActual.mzk1Lemma22_fullShape_gate", "PROVED (stage4)"),
    ("h22 binding", "lemma22FullStatementShape_unconditional + thm25_of_full2_and_24", "PROVED (this file)"),
    ("[Mzk1] Thm 2.5 conclusion", "thm25_of_lemma24_and_geometricCore", "PROVED modulo Lemma 2.4 + GeometricCore"),
    ("Lemma 2.4 shape", "Lemma24Shape (named hypothesis)", "NAMED HYPOTHESIS (2.4 D/M residual)"),
    ("GeometricCore", "Mzk1GeometricCoreRecast (real-structure skeleton)", "NAMED HYPOTHESIS (class-D paper input)"),
    ("paper-level Thm 2.5", "corpus statement 207-221 / proof 222-281", "conditional only on Lemma 2.4 + GeometricCore; no further closure claim") ]

theorem mzk1Thm25UnconditionalRows_length : mzk1Thm25UnconditionalRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm25UnconditionalActual

end
