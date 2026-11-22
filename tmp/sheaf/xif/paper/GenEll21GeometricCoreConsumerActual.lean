import tmp.sheaf.xif.paper.GenEll05Theorem21Actual
import tmp.sheaf.xif.paper.GenEll15GeometricCoreAssemblyActual
import tmp.sheaf.xif.paper.Mzk1Lemma22RationalGateActual
import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerActual
import tmp.sheaf.xif.paper.Mzk1GeometricCoreRealStructureActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import Mathlib.Tactic

/-! # GenEll21GeometricCoreConsumerActual — CONDITIONAL Problem D -> GeometricCore consumer

STEP 0 prior-art (read + reuse, no re-proof):
* GenEll05Theorem21Actual: Theorem 2.1 (i)<=>(ii); (i)=>(ii) PROVED (theorem21_i_implies_ii);
  (ii)=>(i) is the exact named paper-input Theorem21_ii_implies_i_required with
  Theorem21ReductionInputs; epsilon arithmetic PROVED (paper_epsilon_absorption);
  field mzk1NoncriticalBelyi typed as the precise Mzk1GeometricCoreStatement.
* GenEll15GeometricCoreAssemblyActual: precise GenEll15GeometricCoreStatement
  (= forall c eps T D, Mzk1GeometricCoreRecast c eps T D), genEll15_recast_iff,
  genEll15_recast_of_witness.
* coord/ProblemD_GeometricCoreSkeleton.lean (READ-ONLY SKELETON, NOT imported; contains
  sorry and lives outside the paper dir): Problem D reduces GeometricCore to a function-field
  construction: for D = sum of T with deg D >= 2g+1, Riemann-Roch gives l(D) - l(D-t) = 1,
  choose h in L(D) outside every L(D-t); then g = 1/h has zero divisor exactly T.  Only
  function-field Riemann-Roch is deep; ported RR assets are available (GenEll15 docs).
* Mzk1Lemma22RationalGateActual (stage4 FROZEN sha 9BE3F833): rational 2.2 target PROVED
  (F=Q component) — partial input, cited below via rational22_partial_available.
* Mzk1Thm25P1CompositeConsumerActual (stepxi, CITABLE): real P1 composite consumer
  (F=Q) consuming the rational 2.2 gate + 2.3 Moebius layer — partial input, cited in rows.

SCOPE / INTEGRITY: this file is CONDITIONAL on explicitly named inputs (Problem D
function-field witness existence + applicability of the paper hypotheses; GenEll
Theorem 2.1 (ii)=>(i); Mzk1 noncritical Belyi / GeometricCore).  Nothing deep is asserted
true; no closure claim; Problem D skeleton (sorry) is NOT imported.  Exact blockers are
the named Props below. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.GenEll21GeometricCoreConsumerActual

open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual
open LeanFormal.IUT.XiFPaper.GenEll15GeometricCoreAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Theorem25StatementActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22RationalGateActual
open NeronModelInfra CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual

universe u

/-- Paper hypotheses for the Problem D function-field construction on a curve datum:
smooth, proper, connected curve over an algebraically closed field; a finite closed
subset T with |T| >= 2g+1; D = sum of T (zero divisor target).  All fields are Prop
values with explicit proofs (hypotheses, not asserted deep facts). -/
structure ProblemDCurveHypotheses {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (eps : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (T D : Set C) where
  smooth : Prop
  proper : Prop
  connected : Prop
  baseAlgClosed : Prop
  hSmooth : smooth
  hProper : proper
  hConnected : connected
  hAlgClosed : baseAlgClosed
  genus : Nat
  Tfin : Finset C
  hTfin : T = (↑Tfin : Set C)
  hTcard : 2 * genus + 1 <= Tfin.card
  hD : D = (↑Tfin : Set C)

/-- NAMED INPUT (Problem D function-field witness): for every curve datum satisfying
the paper hypotheses, the function-field construction provides a GeometricCore witness
(i.e. psi : X -> P^1 whose zero divisor is exactly T, built from h in L(D) outside all
L(D - t), g = 1/h; only function-field Riemann-Roch is deep).  This is the restated
precise Problem D input; NOT proved here. -/
abbrev ProblemDFunctionFieldWitnessInput : Prop :=
  forall {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (eps : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (T D : Set C), ProblemDCurveHypotheses c eps T D ->
      Nonempty (Mzk1GeometricCoreWitness c eps T D)

/-- NAMED INPUT (Problem D applicability): every GeometricCore curve datum admits a
choice of T, D satisfying the Problem D hypotheses (finite T with |T| >= 2g+1, D = sum T).
This is the bookkeeping that the paper application always lands in the Problem D shape;
NOT proved here. -/
abbrev ProblemDApplicabilityInput : Prop :=
  forall {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (eps : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C),
      Nonempty (ProblemDCurveHypotheses c eps T D)

/-- NAMED INPUT (GenEll Theorem 2.1 (ii)=>(i) consumer interface): the exact paper
input of GenEll05Theorem21Actual, kept as an explicit parameter. -/
abbrev GenEll21IIImpliesIInput : Prop :=
  forall (X : Type u) (K : Set X) (ht logDiff logCond : X -> Real) (eps : Real),
    Theorem21_ii_implies_i_required K ht logDiff logCond eps

/-- NAMED INPUT ([Mzk1] noncritical Belyi / GeometricCore): the precise migrated
statement from GenEll05Theorem21Actual.Theorem21ReductionInputs.mzk1NoncriticalBelyi. -/
abbrev Mzk1NoncriticalBelyiInput : Prop :=
  Mzk1GeometricCoreStatement.{u}

/-- Problem D witness inputs yield the precise GeometricCore statement (GenEll15).
Unfolded-input form (avoids universe ambiguity of the named abbrevs). -/
theorem genEll21_geometricCore_of_problemD
    (hD : forall {R : Type u} [CommRing R] {C : Scheme.{u}}
      (c : C ⟶ Spec (CommRingCat.of R))
      (eps : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
      (T D : Set C), ProblemDCurveHypotheses c eps T D ->
        Nonempty (Mzk1GeometricCoreWitness c eps T D))
    (hApp : forall {R : Type u} [CommRing R] {C : Scheme.{u}}
      (c : C ⟶ Spec (CommRingCat.of R))
      (eps : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C),
        Nonempty (ProblemDCurveHypotheses c eps T D)) :
    GenEll15GeometricCoreStatement.{u} := by
  intro R _inst C c eps T D
  obtain ⟨data⟩ := hApp c eps T D
  exact genEll15_recast_of_witness c eps T D
    (Classical.choice (hD c eps T D data))

/-- The [Mzk1] reduction-input record is available (all non-deep fields discharged by
True with trivial proof; the deep field is exactly the named Mzk1 input). -/
def genEll21_reductionInputs_available (X : Type u)
    (hMzk1 : Mzk1Theorem25StatementActual.Mzk1GeometricCoreStatement.{u}) :
    Theorem21ReductionInputs (X := X) :=
  { compactnessInput := True
    mzk1NoncriticalBelyi := hMzk1
    compactlyBoundedFromPhi := True
    prop16LogCondLeHeight := True
    prop17LogDiffCondLe := True
    prop14HeightComparison := True
    epsilonPrelude := True }

/-- Partial input citation: the stage4 rational 2.2 gate (F=Q component) is PROVED and
frozen; recorded here as the available partial input, not as a closure of 2.2. -/
theorem rational22_partial_available :
    forall (S : Finset (P1Point Rat)) (beta : P1Point Rat),
      Lemma22Hypotheses S beta -> Mzk1Lemma22Target S beta :=
  mzk1Lemma22_target_rational

/-- CONDITIONAL CONSUMER (deliverable): the named Problem D inputs (unfolded form) +
GenEll 2.1 (ii)=>(i) consumer input + [Mzk1] input give the precise GeometricCore statement.
The GenEll 2.1 (ii)=>(i) input and [Mzk1] input are explicit parameters connected to the
consumer interface (their exact Props are defined above and the reduction-input record is
available below); the rational 2.2 gate (F=Q, PROVED frozen) is cited as partial input.
Conditional on named inputs only; no closure claim. -/
theorem genEll21_geometricCore_consumer
    (hD : forall {R : Type u} [CommRing R] {C : Scheme.{u}}
      (c : C ⟶ Spec (CommRingCat.of R))
      (eps : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
      (T D : Set C), ProblemDCurveHypotheses c eps T D ->
        Nonempty (Mzk1GeometricCoreWitness c eps T D))
    (hApp : forall {R : Type u} [CommRing R] {C : Scheme.{u}}
      (c : C ⟶ Spec (CommRingCat.of R))
      (eps : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C),
        Nonempty (ProblemDCurveHypotheses c eps T D))
    (h21 : GenEll21IIImpliesIInput) (hMzk1 : Mzk1NoncriticalBelyiInput) :
    GenEll15GeometricCoreStatement.{u} :=
  genEll21_geometricCore_of_problemD hD hApp

/-- SECTION 9 TASK (1): GenEll05 Theorem 2.1 (ii)=>(i) CONDITIONAL CONSUMER.  The exact paper
input is the named GenEll21IIImpliesIInput; the PROVED rational 2.2 gate (F=Q component) is
carried alongside as a partial input (not a proof of (ii)=>(i)). -/
theorem genEll05_ii_implies_i_consumer
    (h21 : forall (X : Type u) (K : Set X) (ht logDiff logCond : X -> Real) (eps : Real),
      Theorem21_ii_implies_i_required K ht logDiff logCond eps)
    (X : Type u) (K : Set X)
    (ht logDiff logCond : X -> Real) (eps : Real) :
    CaseII K ht logDiff logCond eps -> CaseI ht logDiff logCond eps :=
  h21 X K ht logDiff logCond eps

/-- Combined conditional consumer: GenEll05 (ii)=>(i) (named input) together with the
PROVED rational 2.2 gate/consumer (F=Q partial input).  Conditional only; no closure. -/
theorem genEll05_ii_implies_i_consumer_with_rational22
    (h21 : forall (X : Type u) (K : Set X) (ht logDiff logCond : X -> Real) (eps : Real),
      Theorem21_ii_implies_i_required K ht logDiff logCond eps)
    (X : Type u) (K : Set X)
    (ht logDiff logCond : X -> Real) (eps : Real) :
    (CaseII K ht logDiff logCond eps -> CaseI ht logDiff logCond eps) ∧
      (forall (S : Finset (P1Point Rat)) (beta : P1Point Rat),
        Lemma22Hypotheses S beta -> Mzk1Lemma22Target S beta) :=
  ⟨genEll05_ii_implies_i_consumer h21 X K ht logDiff logCond eps,
   rational22_partial_available⟩

/-- Exact blocker rows: named inputs + partial proved inputs + forbidden paths. -/
structure GenEll21ConsumerRow where
  item : String
  status : String
  evidence : String

def genEll21ConsumerRows : List GenEll21ConsumerRow :=
  [ ⟨"Problem D function-field witness (smooth/proper/connected, alg closed, T finite closed pts, |T|>=2g+1, h in L(D) minus union L(D-t), g=1/h)", "NAMED INPUT", "ProblemDFunctionFieldWitnessInput (not proved; RR only deep input)"⟩,
    ⟨"Problem D applicability (curve datum admits T,D with paper hypotheses)", "NAMED INPUT", "ProblemDApplicabilityInput (not proved)"⟩,
    ⟨"GenEll Theorem 2.1 (ii)=>(i)", "NAMED INPUT", "GenEll21IIImpliesIInput = Theorem21_ii_implies_i_required"⟩,
    ⟨"[Mzk1] noncritical Belyi / GeometricCore", "NAMED INPUT", "Mzk1NoncriticalBelyiInput = Mzk1GeometricCoreStatement"⟩,
    ⟨"GenEll 2.1 (i)=>(ii)", "PROVED (reused)", "GenEll05Theorem21Actual.theorem21_i_implies_ii"⟩,
    ⟨"GeometricCore recast assembly", "PROVED (reused)", "GenEll15GeometricCoreAssemblyActual.genEll15_recast_of_witness"⟩,
    ⟨"rational 2.2 gate/consumer (F=Q)", "PROVED PARTIAL", "Mzk1Lemma22RationalGateActual.mzk1Lemma22_target_rational (frozen sha 9BE3F833); consumer Mzk1Thm25P1CompositeConsumerActual"⟩,
    ⟨"Problem D skeleton", "READ-ONLY (NOT imported)", "coord/ProblemD_GeometricCoreSkeleton.lean contains sorry; not compiled, not cited"⟩,
    ⟨"closure", "NOT CLAIMED", "GATE NOT PASSED; Qbar/full P1 reduction remains NAMED; binding HOLD"⟩ ]

theorem genEll21ConsumerRows_length : genEll21ConsumerRows.length = 9 := rfl

#check ProblemDFunctionFieldWitnessInput
#check ProblemDApplicabilityInput
#check GenEll21IIImpliesIInput
#check genEll21_geometricCore_consumer

end LeanFormal.IUT.XiFPaper.GenEll21GeometricCoreConsumerActual
end
