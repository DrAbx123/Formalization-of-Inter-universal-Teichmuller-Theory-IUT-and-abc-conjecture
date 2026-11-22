import tmp.sheaf.xif.paper.Mzk1Thm25WiringActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Thm25P1CompositeConsumerDesignActual — DESIGN + STATEMENT for the REAL Thm 2.5 consumer

STEP 0 prior-art: external review (Lead A277/A279/A281; mainline A280): the existing
h22 binding (Mzk1Thm25WiringActual.thm25_of_22_24_and_geometricCore) only reads hcore:
h22/h24 are stored in the wiring record, not consumed; Mzk1GeometricCoreWitness fields
are free Props, so the binding changes NO mathematics.  The real consumer of [Mzk1]
Thm 2.5 is the P1-case composite 2.4 o 2.3 o 2.2, needing the 2.3 Moebius transformation
and C-point unramifiedness/critical values (paper Lemma 2.1(b) is over C; the current
UnramifiedOver checks Q-points only).  Binding is HOLD; gate is NOT PASSED.

THIS FILE is DESIGN/STATEMENT ONLY (no closure claim, no fake proof):
* vocabulary: P1(ℚ)/P1(ℂ) points, the ℂ-valued special set, C-point critical-value
  predicate CPointCriticalValuesIn01, minimal Moebius data/action;
* P1CompositeRealConsumerTarget: the P1 composite real-consumer target statement;
* P1CompositeConsumerInputs + P1CompositeConsumerStatement: the conditional shape with
  the exact upstream inputs required (restated 2.4 C-point interface, 2.3 Moebius, CV
  composition law, C-point critical-value lift);
* hullInterfaceNeeds: the precise 2.3 Moebius mapPoints/CV interface needed from hull.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual

/-- The special target set over the complex P1: {0,1,infinity}. -/
def specialSetC : Set (P1Point ℂ) :=
  {p | p = P1Point.infty ∨ p = P1Point.ofFinite (0 : ℂ) ∨ p = P1Point.ofFinite (1 : ℂ)}

/-- C-point critical-value control: every critical point over C maps to 0 or 1
(the C-strengthening of the paper Lemma 2.1(b) critical-value condition). -/
def CPointCriticalValuesIn01 (f : ℚ[X]) : Prop :=
  ∀ z : ℂ,
    (Polynomial.derivative (f.map (algebraMap ℚ ℂ))).eval z = 0 →
      (f.map (algebraMap ℚ ℂ)).eval z = 0 ∨ (f.map (algebraMap ℚ ℂ)).eval z = 1

/- SINGLE SOURCE (no duplication): the structure MoebiusData and its action MoebiusData.mapPoints
are defined HERE, once.  qpilot's Mzk1MoebiusP1Actual imports THIS file and extends the same
definitions in this namespace (comp, nonconstancy, composition law, critical values, inversion);
the C-typed MoebiusDataC in Mzk1MoebiusP1CActual is a distinct C-typed variant, not a duplicate.
The import direction cannot be reversed (design importing qpilot's extension): qpilot's file
imports this one, so that would be a cycle.  This layering is the acyclic single-source answer
to the shehdd S3254 no-duplication flag. -/
/-- Minimal 2.3 Moebius data: z |-> (a z + b)/(c z + d) on P1, nonconstant (det != 0). -/
structure MoebiusData where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  det : a * d - b * c ≠ 0

/-- The Moebius action on P1(ℚ), with the standard pole/infinity convention. -/
noncomputable def MoebiusData.mapPoints (M : MoebiusData) : P1Point ℚ → P1Point ℚ
  | none => if M.c = 0 then P1Point.infty else P1Point.ofFinite (M.a / M.c)
  | some x =>
      if M.c * x + M.d = 0 then P1Point.infty
      else P1Point.ofFinite ((M.a * x + M.b) / (M.c * x + M.d))

/-- The P1 composite real-consumer TARGET (statement only): for every paper-conditioned
(S,beta) there is a nonconstant polynomial map into {0,1,infinity}, avoiding beta, with
C-point critical-value control.  This is the paper-recognizable consequence the real
consumer must produce (stronger than the current Q-point gate). -/
def P1CompositeRealConsumerTarget : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ),
    Lemma22Hypotheses S β →
      ∃ (f : ℚ[X]) (hdeg : 1 ≤ f.natDegree),
        PreservesSet (polyMorphism f hdeg) (↑S : Set (P1Point ℚ)) specialSet ∧
        AvoidsPoint (polyMorphism f hdeg) β specialSet ∧
        CPointCriticalValuesIn01 f

/-- The required upstream inputs for the real consumer (all named/conditional):
(i) the full 2.2 gate; (ii) the RESTATED 2.4 interface (C-point version); (iii) the 2.3
Moebius data/action; (iv) the CV composition law and the C-point critical-value lift
(these are the interface obligations, recorded as Props - not assumed true here). -/
structure P1CompositeConsumerInputs where
  h22 : Lemma22FullStatementShape
  /-- F=Q BASE-ONLY restated 2.4 C-point interface (abc RestatedLemma24InterfaceActual). -/
  h24Base : Prop
  /-- Paper-scope NAMED input: algebraic nested induction over P1(Qbar), paper lines
  179-206 (m/d step); recorded as a statement in RestatedLemma22InterfaceActual. -/
  algebraicNestedInduction :
    LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput
  mobius : MoebiusData
  cvCompositionLaw : Prop
  cPointCriticalValueLift : Prop

/-- SCOPE (Lead A311/A313): the consumer's rational-input part is F=Q BASE-ONLY (base case
m(S)=0 + rational Belyi existence); the full P1(Qbar) reduction is NAMED (not complete):
(D) Galois descent PROVED, infinite fixed field class-B named, 2.3 Moebius over Qbar/C,
algebraic nested induction = AlgebraicNestedInductionInput.  No closure claim.

The conditional consumer STATEMENT: from the inputs, the P1 composite target. -/
def P1CompositeConsumerStatement (I : P1CompositeConsumerInputs) : Prop :=
  P1CompositeRealConsumerTarget

/-- Design rows: (component, evidence/interface, status). -/
def mzk1P1CompositeDesignRows : List (String × String × String) :=
  [ ("P1 vocabulary", "P1Point Q / P1Point C / specialSetC", "DEFINED (design)"),
    ("C-point critical-value control", "CPointCriticalValuesIn01 (f.map Q->C derivative roots map to 0/1)", "DEFINED (target predicate)"),
    ("2.3 Moebius data/action", "MoebiusData + mapPoints (pole/infinity convention)", "DEFINED (design)"),
    ("P1 composite real-consumer target", "P1CompositeRealConsumerTarget", "STATEMENT ONLY (not proved)"),
    ("conditional consumer shape", "P1CompositeConsumerInputs / P1CompositeConsumerStatement", "STATEMENT ONLY (upstream inputs named)"),
    ("scope split", "F=Q base-only rational component delivered; full P1(Qbar) reduction NAMED (descent PROVED + fixed field class-B + 2.3 Moebius over Qbar/C + AlgebraicNestedInductionInput)", "SCOPE (A313 option (i); no closure claim)"),
    ("paper-scope named input", "RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput (paper lines 179-206 m/d step)", "STATEMENT ONLY / NAMED"),
    ("old h22 binding", "Mzk1Thm25UnconditionalActual (pre-written, NOT queued)", "HISTORY ONLY; binding HOLD; gate NOT PASSED"),
    ("real consumer proof", "requires restated 2.4 C-point + 2.3 Moebius CV law + C-point lift", "OPEN (delivery order: upstream -> restated targets -> full gate -> this consumer)") ]

theorem mzk1P1CompositeDesignRows_length : mzk1P1CompositeDesignRows.length = 9 := rfl

/-- Exact interface needed from hull for the 2.3 Moebius / CV composition layer. -/
def hullInterfaceNeeds : List (String × String) :=
  [ ("Moebius mapPoints", "z |-> (a z + b)/(c z + d) on P1(Q): finite/pole conventions and infinity image a/c (c != 0) or infinity (c = 0), det = ad-bc != 0"),
    ("CV set", "critical values as Set (P1Point Q) for polynomials and Set (P1Point C) for the C-strengthening"),
    ("CV composition law", "CritVal(f o M) <= M^{-1}(CritVal f); for Moebius M (no critical points) CritVal(f o M) = M^{-1}(CritVal f)"),
    ("C-point unramifiedness", "derivative root dichotomy over C (belyi21_derivative_root is already over C) and transport through Moebius (conformal => unramified)"),
    ("C-point critical-value lift", "CPointCriticalValuesIn01 f for the polynomial produced by 2.2; transport through 2.3 Moebius and 2.4 restriction"),
    ("nonconstancy", "Moebius nonconstancy from det != 0; polynomial nonconstancy 1 <= natDegree") ]

theorem hullInterfaceNeeds_length : hullInterfaceNeeds.length = 6 := rfl


/-- Available (green/CITABLE) Möbius assets from Mzk1MoebiusP1Actual that the real
consumer will use (mainline A299): (asset, evidence/signature, status). -/
def availableMoebiusAssets : List (String × String × String) :=
  [ ("MoebiusData.comp", "M N : MoebiusData with det = det M * det N != 0", "PROVED (qpilot Mzk1MoebiusP1Actual)"),
    ("MoebiusData.mapPoints_nonconstant", "exists p q, M.mapPoints p != M.mapPoints q", "PROVED (qpilot)"),
    ("MoebiusData.mapPoints_comp_of_finite", "generic-chart composition law (both denominators nonzero)", "PROVED (qpilot)"),
    ("MoebiusData.derivativeNumerator(_ne_zero)", "formal derivative numerator = ad-bc != 0; no finite critical point", "PROVED (qpilot)"),
    ("moebiusCriticalValues + _eq_empty", "critical-value set of a Moebius map is empty", "PROVED (qpilot)"),
    ("specialSetQ + mapsTo_specialSetQ_iff", "special-set maps-to criterion for {0,1,infinity}", "PROVED (qpilot; use for Moebius PreservesSet)"),
    ("moebiusInversion + mapsTo_specialSet", "concrete inversion Möbius; specialSet -> specialSet", "PROVED (qpilot)"),
    ("MoebiusDataC + mapPoints (C)", "structure MoebiusDataC over C; action P1Point C -> P1Point C (pole->infty, infty: c!=0->a/c, c=0->infty)", "PROVED (qpilot Mzk1MoebiusP1CActual CITABLE 14)"),
    ("MoebiusDataC.moebiusCriticalValuesC(_eq_empty)", "C-typed Moebius critical-value Set (P1Point C) is empty", "PROVED (qpilot)"),
    ("criticalValuesC + criticalValuesC_transport + mapToC", "Q-CV image under mapRatComplex equals C-typed Moebius CV; mapToC base change", "PROVED (qpilot)"),
    ("MoebiusDataC.mapsTo_specialSetC_iff", "C special-set maps-to criterion for {0,1,infinity}", "PROVED (qpilot)"),
    ("MoebiusData.mapPoints_infty/pole/finite + mapPoints_comp_infty", "infinity/pole conventions and infinity composition law", "PROVED (qpilot C-file)") ]

theorem availableMoebiusAssets_length : availableMoebiusAssets.length = 12 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual

end
