import Mathlib
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.RestatedLemma24InductionActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24UnionActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual

/-- The number-field closure F = Qbar (paper [Mzk1] Lemma 2.4 input field). -/
abbrev F : Type := AlgebraicClosure ℚ

/-- Cast a rational point of P^1(Q) into P^1(F). -/
def castRatPoint : P1Point ℚ → P1Point F :=
  fun r => match r with
    | none => P1Point.infty
    | some q => P1Point.ofFinite (algebraMap ℚ F q)

/-- Evaluation of a polynomial f over F on P^1(F), with f(infinity) = infinity. -/
def polyEvalP1K (f : Polynomial F) : P1Point F → P1Point F :=
  fun p => p.map (fun x => Polynomial.eval x f)

/-- **Paper-scope [Mzk1] Lemma 2.4 target (statement only)**: for finite S contained in
P^1(Qbar) and beta in P^1(Qbar) outside S, there are a finite RATIONAL target set
Sphi in P^1(Q) and a nonconstant polynomial f with coefficients in F = Qbar such that f
maps S into Sphi (under the canonical cast P^1(Q) -> P^1(F)), keeps beta outside Sphi,
and every critical value of f at an F-point lies in Sphi.  This is the ALGEBRAIC-input
paper scope (Lemma 2.4 lines 144-160); the rational-input restated interface elsewhere is
only the m(S)=0 base component. -/
def PaperScopeLemma24Target (S : Finset (P1Point F)) (β : P1Point F) : Prop :=
  ∃ (Sphi : Finset (P1Point ℚ)) (f : Polynomial F),
    0 < f.natDegree ∧
      (∀ p ∈ S, ∃ r ∈ Sphi, polyEvalP1K f p = castRatPoint r) ∧
      (¬ ∃ r ∈ Sphi, polyEvalP1K f β = castRatPoint r) ∧
      (∀ z : F, Polynomial.aeval z (Polynomial.derivative f) = 0 →
        ∃ r ∈ Sphi, castRatPoint r = P1Point.ofFinite (Polynomial.aeval z f))

/-- Statement-only paper-scope Lemma 2.4 (no proof claimed). -/
def PaperScopeLemma24Statement : Prop :=
  ∀ (S : Finset (P1Point F)) (β : P1Point F), β ∉ S → PaperScopeLemma24Target S β

/-- **Named class-B paper input: algebraic nested (m,d) induction** (paper [Mzk1] Lemma
2.4 lines 163-206).  Packages the paper's nested induction on (m(S), d(S)) — Galois
closure, minimal-polynomial f0, S' = f0(S) union f0(S0), field-degree drop and CV
invariant — in the fixed measure given by Mzk1Lemma24UnionActual.mOfPoints/dOfPoints on
Qbar point sets.  Registered as a class-B named input; the rational-input base component
is BetaAvoidingBelyiBaseInput, and S1a/S1b/S2/S2-i are the extent of the proved measure
machinery. -/
def AlgebraicNestedInductionInput : Prop := PaperScopeLemma24Statement

/-- Rational-input scope record (Lead decision): the restated P^1(Q)-typed interfaces are
ONLY the m(S)=0 base component, not the paper obligation. -/
def RationalInputScopeRecord : Audit.Obligation :=
  { id := "MZK1.lemma24.rational-input-scope"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-160; Lead scope decision (A311 confirmation)"
    status := Audit.VerificationStatus.interface
    note := "SCOPE (Lead-confirmed against paper text): paper Lemma 2.4 inputs are S subset P1(Qbar) finite, beta in Qbar minus S, conclusion exists Sphi subset P1(Q) and phi defined over the number field F of S,beta with phi(S) subset Sphi, phi(beta) in P1(Q) minus Sphi, phi unramified over P1 minus Sphi; proof 163-206 = normalization x -> x - beta + Galois closure + NESTED INDUCTION on (m,d) with alpha0 in S not rational, f0 = minpoly, S' = f0(S) union f0(S0), [Q(alpha'):Q] < d0 and m(S')/d(S') decrease. Therefore the restated P1(Q)-typed interfaces (RestatedLemma24InterfaceActual / RestatedLemma24InductionActual / RestatedLemma24CVLawActual) are the rational-input = m(S)=0 BASE component ONLY and do NOT close the paper obligation. Paper-scope target and named papers input AlgebraicNestedInductionInput (this file) record the algebraic layer. No closure claim; binding HOLD; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.restated-induction" ]
    sorryItems :=
      [ "AlgebraicNestedInductionInput (paper 163-206 nested (m,d) induction)",
        "paper-scope target with F-defined phi and rational S_phi" ] }

/-- Status: paper-scope statement interface + named class-B implicit input filed; asserts
no closure. -/
def PaperScopeLemma24Status : Audit.Obligation :=
  { id := "MZK1.lemma24.paper-scope"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-206"
    status := Audit.VerificationStatus.interface
    note := "FILED (statement only): F := AlgebraicClosure Q; castRatPoint; polyEvalP1K; PaperScopeLemma24Target (algebraic inputs S subset P1(Qbar), beta in Qbar minus S; output Sphi subset P1(Q), nonconstant f over F, f(S) subset Sphi, f(beta) outside, critical values at F-points in Sphi); PaperScopeLemma24Statement; AlgebraicNestedInductionInput (named class-B paper input for the 163-206 nested (m,d) induction with fixed measure mOfPoints/dOfPoints and CV invariant). Proved assets retained: S1a/S1b/S2/S2-i, CV law/CVCompat, descent finite-Galois, L2.3 normalization+transfer, rational base attempt inputs. Rational-input layer explicitly marked base-only (RationalInputScopeRecord). No closure claim; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.rational-input-scope" ]
    sorryItems :=
      [ "AlgebraicNestedInductionInput (class-B named)",
        "base provider at paper scope",
        "step provider/assembly at paper scope" ] }

#check PaperScopeLemma24Target
#check AlgebraicNestedInductionInput
end LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
end
