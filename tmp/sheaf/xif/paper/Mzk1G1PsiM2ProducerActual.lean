import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1Consumer24AdapterUnconditionalActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Tactic

/-!
# ⑥ M2 producer for B1: the single-protected-point (beta = 0) reduction

Route mapping (Lead-verified lines):
* route §4.1 L273-278: s0 has only simple zeros, hence psi^{-1}(0) = D_T (B2) and
  D_T = sum_{t in T} [t], so psi maps every point of T to 0.
* route §4.3 L300: with S1 = psi(S) union Branch(psi) (note 0 not in S1 by B2), the task
  is to find h mapping S1 and its own branch values into {0,1,infty} while h(0) AVOIDS
  these three points.  Hence beta = 0 is the ONLY protected point: the T-avoidance in B1 is
  exactly phi(t) = h(psi(t)) = h(0) not in {0,1,infty}, given by the single-beta
  protection condition.  No multi-beta version is needed.

So the M2 recursion (route §4.3 steps 1-6) only ever protects ONE point beta, and the
terminating step (beta finite rational) is the M1 base case
  Mzk1Consumer24AdapterUnconditionalActual.finiteBetaCorrectedBase_proved.

This file records the base-case bridge (proved, three axioms) and the interface shape of the
recursion.  The recursion itself (steps 1-6: measure, Galois closure, rational Mobius f0,
critical values S2, strict measure decrease, composition) is the remaining M2 work; it is
NOT stated here to avoid a conditional interface.
-/

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2ProducerActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- M1 BASE CASE (route §4.3 L302 + terminal step of the §4.3 recursion): for every finite
set S of rational points and every finite rational value b outside S, the restated
Lemma 2.4 target holds.  This is the unconditionally proved old consumer-24 base case,
whose axioms were verified to be [propext, Classical.choice, Quot.sound] by probe
(_ProbeConsumer24AxActual). -/
theorem mzk1Lemma24Target_of_finite (S : Finset (P1Point ℚ)) (b : ℚ)
    (hb : P1Point.ofFinite b ∉ S) :
    Mzk1Lemma24Target S (P1Point.ofFinite b) :=
  Mzk1Consumer24AdapterUnconditionalActual.finiteBetaCorrectedBase_proved S b hb

/-- The base case covers the protected point beta = 0 (the only protected point needed for
B1, route §4.3 L300), as long as 0 is not in S. -/
theorem mzk1Lemma24Target_of_zero (S : Finset (P1Point ℚ))
    (hb : (P1Point.ofFinite (0 : ℚ) : P1Point ℚ) ∉ S) :
    Mzk1Lemma24Target S (P1Point.ofFinite (0 : ℚ)) :=
  mzk1Lemma24Target_of_finite S 0 hb

/- The M2 recursion target (route §4.3 steps 1-6), stated for reference only in this
comment: for ALL finite S and all beta with beta not in S, the restated Lemma 2.4 target
holds.  Its proof is the remaining M2 work; we do NOT introduce it as a conditional
interface. -/

/-!
## M2 recursion scaffold (route §4.3 L304-317): algebraic-point layer

The recursion runs on ALGEBRAIC points of P^1 presented by their monic minimal polynomial
over Q (the rational-value interface P1Point Q only covers degree 1, while Branch(psi)
contains non-rational algebraic points such as the images of the n-th roots of unity).

Measure: (max reduced degree, total degree) lexicographic, where the degree of an
algebraic point is the natDegree of its monic minimal polynomial.  The recursion reduces all
degrees to 1; then the data transports to P1Point Q and the M1 base case
(mzk1Lemma24Target_of_finite) applies -- exactly the route §4.3 L302 restriction.
-/

/-- An algebraic point of P^1 presented by its monic minimal polynomial over Q. -/
structure AlgPoint where
  /-- The monic minimal polynomial. -/
  minpoly : Polynomial ℚ
  /-- It is monic. -/
  monic : minpoly.Monic

namespace AlgPoint

/-- The degree of an algebraic point (degree of its monic minimal polynomial). -/
def deg (p : AlgPoint) : ℕ := p.minpoly.natDegree

/-- The reduced degree used in the lexicographic recursion measure.  For a monic minimal
polynomial this is the same as the degree; the separate name keeps the route's pair. -/
def redDeg (p : AlgPoint) : ℕ := p.minpoly.natDegree

/-- The rational point b, presented as the algebraic point with minimal polynomial X - b. -/
def ofRat (b : ℚ) : AlgPoint where
  minpoly := Polynomial.X - Polynomial.C b
  monic := Polynomial.monic_X_sub_C b

end AlgPoint

/-- The recursion measure (max reduced degree, total degree) of the finite list S of
algebraic points with the protected point beta (route §4.3 L304-317).  A list presentation
is used to avoid requiring decidable equality on the structure. -/
noncomputable def muMeasure (S : List AlgPoint) (β : AlgPoint) : ℕ × ℕ :=
  ((β :: S).foldr (fun p m => max p.redDeg m) 0,
    (β :: S).foldr (fun p s => p.redDeg + s) 0)

/-- The lexicographic order on the recursion measure is well founded (Mathlib
WellFounded.prod_lex with wellFounded_lt on Nat), giving termination of the route §4.3
recursion. -/
theorem muMeasure_wf :
    WellFounded (Prod.Lex (· < ·) (· < ·) : ℕ × ℕ → ℕ × ℕ → Prop) :=
  WellFounded.prod_lex (wellFounded_lt (α := ℕ)) (wellFounded_lt (α := ℕ))

#print axioms mzk1Lemma24Target_of_finite
#print axioms mzk1Lemma24Target_of_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2ProducerActual
