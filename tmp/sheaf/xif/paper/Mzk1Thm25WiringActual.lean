import tmp.sheaf.xif.paper.Mzk1Thm25ConclusionActual
import tmp.sheaf.xif.paper.Mzk1Theorem25StatementActual
import tmp.sheaf.xif.paper.Mzk1Lemma22InductionActual
import tmp.sheaf.xif.paper.Mzk1PolyChainRuleActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StatementShapeActual
import tmp.sheaf.xif.paper.Mzk1Lemma24Proof2Actual
import tmp.sheaf.xif.paper.Mzk1Lemma24GaloisUnion2Actual
import tmp.sheaf.xif.paper.Mzk1Lemma24ConjInvarianceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option linter.defProp false

/-!
# Mzk1Thm25WiringActual — [Mzk1] Theorem 2.5 CONCLUSION WIRING (2.2 + 2.4 + GeometricCore)

STEP 0 prior-art (reuse, no re-proof):
* Mzk1Thm25ConclusionActual (Mzk1Thm25Conclusion; mzk1Thm25Conclusion_of_geometricCore
  PROVED conditional on Mzk1GeometricCoreRecast) + Mzk1GeometricCoreRealStructureActual
  (Mzk1GeometricCoreWitness/Mzk1GeometricCoreRecast real-structure skeleton over ported
  green FiniteMapData/RiemannRochRows);
* Mzk1Theorem25StatementActual (Mzk1GeometricCoreStatement statement-layer interface;
  its Lean body is a placeholder marker — flagged, NOT used as a proof);
* full Lemma 2.2 StatementShape: stage4 chain rule Mzk1PolyChainRuleActual (CITABLE 5:
  polyMapPoints_comp_* / polyUnramifiedAt_comp_*) + Mzk1Lemma22InductionActual
  (Mzk1Lemma22PartialShape, partial_of_shape, comp_partial, mzk1Lemma22_partial_induction
  PROVED) + our Mzk1Lemma22StepConstructionActual (lemma22StepExists_packaged);
  until stage4 lands the FULL StatementShape it is the named hypothesis
  Lemma22FullStatementShape (explicit gate, TODO headline: replace after stage4);
* Lemma 2.4 shape: Mzk1Lemma24StatementShape (P1 interface); citable 2.4 assets
  Mzk1Lemma24Proof2Actual (s3135_lemma24_induction/arithmetic_layer),
  Mzk1Lemma24GaloisUnion2Actual (s3135_conjugateSet_finite/…),
  Mzk1Lemma24ConjInvarianceActual (s3135_minpoly_eq_of_mem_conjugateSet/…);
  used here as the named hypothesis Lemma24Shape;
* corpus: [Mzk1] Thm 2.5 statement lines 207-221 / proof 222-281; Lemma 2.2 lines
  106-135; Lemma 2.4 lines 144-205; Lemma 2.1 ~35-105.

THIS FILE: the conclusion wiring
  (full 2.2 shape) -> (2.4 shape) -> GeometricCore input -> Thm 2.5 conclusion shape,
where the GeometricCore=>conclusion step is the PROVED
mzk1Thm25Conclusion_of_geometricCore, and the 2.2/2.4 rows are explicit named
hypotheses carried by the wiring record (TODO: stage4 replaces the 2.2 hypothesis with
the real chain-rule proof; note the reduction of the paper hypotheses to GeometricCore
is the remaining mathematical content).  No closure claim; no fake consumption claims.

Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual

universe u

/-- [Mzk1] Thm 2.5 GeometricCore paper input (statement-layer interface).
The Lean body of Mzk1GeometricCoreStatement is now the precise forall schema (approved
placeholder patch, CITABLE 6 decls); this definition documents the interface. -/
def Mzk1CorePaperInput : Prop :=
  LeanFormal.IUT.XiFPaper.Mzk1Theorem25StatementActual.Mzk1GeometricCoreStatement.{0}

/-- The PAPER hypotheses of [Mzk1] Lemma 2.2 (stage4-exact): 0 and infinity in S,
all other points positive finite rationals, beta not in S, and the separation
beta/alpha >= 2 for every alpha in S minus {0, infinity}. -/
def Lemma22Hypotheses (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  (P1Point.ofFinite (0 : ℚ) ∈ S) ∧
  (P1Point.infty ∈ S) ∧
  (∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
    ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x) ∧
  (β ∉ S) ∧
  (∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
    ∃ a b : ℚ, p = P1Point.ofFinite a ∧ β = P1Point.ofFinite b ∧ 2 ≤ b / a)

/-- **Full Lemma 2.2 StatementShape** (named hypothesis, the reduction's P1
rational-case case input, PAPER-CONDITIONED as stage4 requires): for every finite S, β
satisfying the Lemma 2.2 hypotheses, there is a nonconstant P1-morphism with the three
Lemma-2.2 properties (Mzk1Lemma22FullShape, stage4 Mzk1Lemma22StatementShapeActual).
TODO headline: stage4 replaces this hypothesis with its proof (expected
mzk1Lemma22_fullShape_gate in Mzk1Lemma22ConditionedActual; binding theorem will be
added to Mzk1Thm25ConsumerActual). -/
def Lemma22FullStatementShape : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ),
    Lemma22Hypotheses S β →
      LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual.Mzk1Lemma22FullShape S β

/-- **Lemma 2.4 shape** (named hypothesis; the reduction to the rational case): for
every finite S, β and target/unramifiedness data there is a nonconstant P1-morphism
with the Lemma-2.4 properties. -/
def Lemma24Shape : Prop :=
  ∀ (K : Type u) [Field K] [DecidableEq K]
    (S : Finset (P1Point K)) (β : P1Point K)
    (targetSet : Set (P1Point K)) (unramifiedAt : P1Point K → Prop),
    Mzk1Lemma24StatementShape K S β targetSet unramifiedAt

/-- The wiring record: the three paper-level inputs together with the [Mzk1] Thm 2.5
conclusion shape read off from a GeometricCore witness (the conclusion step is the
PROVED mzk1Thm25Conclusion_of_geometricCore). -/
structure Thm25WiringRecord {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  /-- full Lemma 2.2 StatementShape (named hypothesis until stage4 replaces it) -/
  lemma22Full : Lemma22FullStatementShape
  /-- Lemma 2.4 shape (named hypothesis; citable 2.4 assets back it) -/
  lemma24 : Lemma24Shape.{u}
  /-- GeometricCore input: the real-structure recast (single named hypothesis) -/
  geometricCore : Mzk1GeometricCoreRecast c ε T D
  /-- the [Mzk1] Thm 2.5 conclusion shape (PROVED from the GeometricCore input) -/
  conclusion : ∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W

/-- **Wiring constructor:** from the 2.2 shape, the 2.4 shape and GeometricCore, build
the wiring record; the conclusion component is the PROVED conditional Thm 2.5
conclusion (mzk1Thm25Conclusion_of_geometricCore). -/
noncomputable def thm25_wiring {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (h22 : Lemma22FullStatementShape) (h24 : Lemma24Shape.{u})
    (hcore : Mzk1GeometricCoreRecast c ε T D) : Thm25WiringRecord c ε T D where
  lemma22Full := h22
  lemma24 := h24
  geometricCore := hcore
  conclusion := mzk1Thm25Conclusion_of_geometricCore c ε T D hcore

/-- **[Mzk1] Theorem 2.5 conclusion wiring (Lead spec (4)):**
(chain rule / full 2.2 shape hypo) -> (2.4 shape hypo) -> GeometricCore input ->
Thm 2.5 conclusion shape.  HONEST: the 2.2/2.4 hypotheses are the named reduction-side
gates (TODO: stage4 replaces the 2.2 one with the real full StatementShape); the
GeometricCore => conclusion step is PROVED. -/
theorem thm25_of_22_24_and_geometricCore {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (h22 : Lemma22FullStatementShape) (h24 : Lemma24Shape.{u})
    (hcore : Mzk1GeometricCoreRecast c ε T D) :
    ∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W :=
  (thm25_wiring c ε T D h22 h24 hcore).conclusion

/-- Wiring rows: ([Mzk1] Thm 2.5 proof component, Lean evidence, status). -/
def mzk1Thm25WiringRows : List (String × String × String) :=
  [ ("GeometricCore => Thm 2.5 conclusion shape", "Mzk1Thm25ConclusionActual.mzk1Thm25Conclusion_of_geometricCore (PROVED)", "PROVED (conditional on GeometricCore recast)"),
    ("full Lemma 2.2 StatementShape (paper-conditioned)", "Lemma22Hypotheses (paper conditions) + Lemma22FullStatementShape := forall S beta, Lemma22Hypotheses S beta -> Mzk1Lemma22FullShape S beta (named hypothesis, corrected per stage4: not the too-strong unconditional form); stage4 PROVED Mzk1PolyChainRuleActual + Mzk1PolyUnramifiedCompositionActual.polyUnramifiedOver_comp + Mzk1Lemma22StatementShapeActual.fullShape_to_partial/fullShape_preserves + Mzk1Lemma22InductionActual partial induction + Mzk1Lemma22StepConstructionActual.lemma22StepExists_packaged", "NAMED HYPOTHESIS (stage4 will prove the paper-conditioned form)"),
    ("Lemma 2.4 shape (reduction to rational case)", "Lemma24Shape (named hypothesis); citable assets Mzk1Lemma24Proof2Actual / Mzk1Lemma24GaloisUnion2Actual / Mzk1Lemma24ConjInvarianceActual", "NAMED HYPOTHESIS (2.4 G/F/D/M items open)"),
    ("GeometricCore input", "Mzk1GeometricCoreRealStructureActual.Mzk1GeometricCoreRecast (real-structure skeleton over ported green FiniteMapData/RiemannRochRows)", "single named hypothesis"),
    ("statement-layer interface", "Mzk1Theorem25StatementActual.Mzk1GeometricCoreStatement (precise forall schema after approved placeholder patch; CITABLE 6 decls)", "interface only; NOT used as proof"),
    ("paper-level Thm 2.5", "corpus statement 207-221 / proof 222-281", "NOT closed; wiring only (no closure claim)") ]

theorem mzk1Thm25WiringRows_length : mzk1Thm25WiringRows.length = 6 := rfl

/-- Remaining discharge (data): (obligation, owner/source). -/
def mzk1Thm25WiringResidual : List (String × String) :=
  [ ("replace Lemma22FullStatementShape by stage4 full 2.2 StatementShape", "stage4 (Mzk1PolyChainRuleActual + induction + lemma22StepExists_packaged)"),
    ("Lemma 2.4 G/F/D/M items", "stage4/mainline (2.4 F/D/M open)"),
    ("reduce paper Thm 2.5 hypotheses (X smooth proper, S,T disjoint) to GeometricCore", "remaining mathematical content (NOT proved here)"),
    ("GeometricCore existence (Mzk1GeometricCoreRecast inhabitant)", "class-D paper input; real-structure skeleton, witness fields explicit Props"),
    ("descent over number field F", "remaining (MISSING)") ]

theorem mzk1Thm25WiringResidual_length : mzk1Thm25WiringResidual.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual

end
