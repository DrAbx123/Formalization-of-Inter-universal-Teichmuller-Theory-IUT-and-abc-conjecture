import Mathlib
import tmp.sheaf.xif.paper.PaperScopeLemma24Actual
import tmp.sheaf.xif.paper.Mzk1Lemma24UnionActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LayerAAlgebraicInductionActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual

/-- Measure pair (m(S), d(S)) of the paper's nested induction, using the proved point
measure functions on Qbar point sets (max/sum of reduced degrees of fields of definition). -/
def paperMeasure (S : Finset Qbar) (hne : S.Nonempty) : Nat × Nat :=
  (mOfPoints S hne, dOfPoints S hne)

/-- **Layer A statement (named class-B paper input)**: the paper [Mzk1] Lemma 2.4 nested
induction on (m(S), d(S)) (lines 179-206) with the algebraic inputs S subset P^1(Qbar),
beta in Qbar minus S: normalization x -> x - beta, Galois closure, alpha0 in S not in
P^1(Q), f0 = minpoly(alpha0), S' = f0(S) union f0(S0), field-degree drop
[Q(alpha'):Q] < d0 and the (m,d) decrease, carrying the CV invariant.  Stated as the
paper-scope target; registered as a named class-B input, not proved. -/
def AlgebraicNestedInductionStatement : Prop := PaperScopeLemma24Statement

/-- The Layer A named input is definitionally the paper-scope target statement. -/
theorem s3135_AlgebraicNestedInduction_iff :
    AlgebraicNestedInductionInput ↔ AlgebraicNestedInductionStatement := Iff.rfl

/-- Rows for Layer A: coverage of the algebraic reduction layers for the paper-scope
Lemma 2.4 (named inputs, proved assets, and scope). -/
def LayerAStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.layerA"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 163-206; Lead A313/A314/A317 scope split"
    status := Audit.VerificationStatus.interface
    note := "LAYER A (paper-scope algebraic reduction, NAMED - not complete): inputs S subset P1(Qbar), beta in Qbar minus S; named class-B AlgebraicNestedInductionInput = AlgebraicNestedInductionStatement (paper 179-206 nested (m,d) induction with normalization/Galois closure/f0 minimal polynomial/S' = f0(S) union f0(S0)/degree drop/CV invariant). Proved assets feeding this layer: finite-Galois descent (Mzk1Lemma24DescentActual, IsGalois.fixedField_top + IntermediateField.mem_bot), infinite fixed-field class-B named (AlgebraicClosureFixedFieldPaperInput), S1a criticalPoint_degree_drop, S1b valueDegreeDrop (stepxi), S2 mOfPoints_lt_of_forall_reducedDegree_lt, S2-i f0S0_m_lt, S3 goal_transport, CV law/CVCompat, L2.3 numeric normalization + hull transfer, measure functions mOfPoints/dOfPoints. Measured by paperMeasure. Coverage statement: F = Q component delivered OR named (BetaAvoidingBelyiBaseInput), full-Qbar reduction named (not complete). No closure claim; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.paper-scope", "MZK1.lemma24.rational-input-scope" ]
    sorryItems :=
      [ "AlgebraicNestedInductionInput (class-B named: paper 179-206 nested (m,d) induction)",
        "2.3 Möbius separation over Qbar/C",
        "2.2 Qbar target (stepxi P1(Q)-typed interface; algebraic version needed)" ] }

#check paperMeasure
#check AlgebraicNestedInductionStatement
#check s3135_AlgebraicNestedInduction_iff
end LeanFormal.IUT.XiFPaper.LayerAAlgebraicInductionActual
end-- revive-bump-2-- layerA-revive-bump
