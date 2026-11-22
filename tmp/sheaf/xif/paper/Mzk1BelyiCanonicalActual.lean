import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.CriticalValues
import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StepConstructionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1BelyiCanonicalActual — canonical TauCeti Belyi consumer for [Mzk1] Lemma 2.1/2.2

STEP 0 prior-art (reuse, no re-proof): qpilot port root
tmp/external/ported/tauceti_belyi_core (quickport, Apache-2.0 attribution):
* TauCeti.Algebra.Polynomial.CriticalValues (EXIT=0, CITABLE 13 decls: criticalValues/
  finite/map/comp_subset/algebraMap…);
* TauCeti.Algebra.Polynomial.Belyi (EXIT=0, CITABLE 13 decls: belyiPolynomial B_{m,n},
  eval_belyiPolynomial, natDegree_belyiPolynomial, rootSet_derivative_belyiPolynomial_subset,
  criticalValues_belyiPolynomial_subset, exists_polynomial_eval/aeval_mem_criticalValues_subset
  = Belyification); drift fixes rootSet_map_eq documented by qpilot.
Our files: Mzk1PolyMapActual (polyMapPoints on P1), Mzk1Lemma22StepConstructionActual
(lemma22Step_card_lt: collision => |image| < |S|), Mzk1GChoiceScaleActual
(rho_pos/rho_lt_one: r = m/(m+n) in (0,1)).
This file BRIDGES the canonical Belyi polynomial to the [Mzk1] Lemma 2.1/2.2 machinery:
* B_{m,n}(0)=B_{m,n}(1)=0 (paper Lemma 2.1 (a)/(c) input at 0,1);
* card collapse |g(S)| < |S| for S containing 0 and 1 (the STEP's main risk, now via the
  canonical Belyi polynomial);
* critical values of B_{m,n} lie in {0,1} (paper Lemma 2.1 (b) root dichotomy at critical
  points; Belyi's critical values);
* Belyification existence (aeval form) for GeometricCore / Lemma 2.4 consumers;
* r = m/(m+n) in (0,1) matching the scale ordering alpha1/alpha2.

HONEST SCOPE: bridge/reuse only; no new Belyi mathematics; the paper-level Lemma 2.1/2.2
remain stage4/stepxi layered statements.  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BelyiCanonicalActual

open Polynomial
open TauCeti
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepConstructionActual

universe u

/-- B_{m,n}(0) = 0 for m >= 1 (paper Lemma 2.1 (a)/(c) input). -/
theorem belyi_eval_zero {m n : ℕ} (hm : 1 ≤ m) :
    (belyiPolynomial ℚ m n).eval 0 = 0 :=
  eval_zero_belyiPolynomial (K := ℚ) (by omega) n

/-- B_{m,n}(1) = 0 for n >= 1. -/
theorem belyi_eval_one (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (belyiPolynomial ℚ m n).eval 1 = 0 :=
  eval_one_belyiPolynomial (K := ℚ) m (by omega)

/-- 0 < natDegree B_{m,n} = m+n for m,n >= 1 (nonconstancy). -/
theorem belyi_natDegree_pos {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    0 < (belyiPolynomial ℚ m n).natDegree := by
  rw [natDegree_belyiPolynomial]
  omega

/-- **Card collapse via the canonical Belyi polynomial:** if 0 and 1 lie in S, the
image of S under B_{m,n} has strictly smaller cardinality (the STEP's |S'| < |S|,
paper Lemma 2.2 proof, now using the canonical Belyi polynomial). -/
theorem belyi_card_collapse {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Finset (P1Point ℚ))
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (h1 : P1Point.ofFinite (1 : ℚ) ∈ S) :
    (S.image (polyMapPoints (belyiPolynomial ℚ m n))).card < S.card :=
  lemma22Step_card_lt S (belyiPolynomial ℚ m n) h0 h1
    (by rw [belyi_eval_zero hm, belyi_eval_one m hn])

/-- Critical values of B_{m,n} lie in {0,1} (paper Lemma 2.1 (b): critical points map
into the special set). -/
theorem belyi_criticalValues_subset (m n : ℕ) :
    (belyiPolynomial ℚ m n).criticalValues ℚ ⊆ ({0, 1} : Set ℚ) :=
  criticalValues_belyiPolynomial_subset ℚ m n

/-- **Belyification existence (canonical TauCeti form):** for a finite integral set S
over ℚ there is a nonconstant polynomial q whose values on S and critical values lie in
{0,1} (the Belyi reduction used by [Mzk1] Lemma 2.2/2.4 and GeometricCore). -/
theorem belyi_exists_polynomial_aeval {K : Type u} [Field K] [Algebra ℚ K]
    {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} :=
  exists_polynomial_aeval_mem_criticalValues_subset hS

/-- Rational Belyification (the Finset ℚ form). -/
theorem belyi_exists_polynomial_eval (S : Finset ℚ) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, q.eval s ∈ ({0, 1} : Set ℚ)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} :=
  exists_polynomial_eval_mem_criticalValues_subset S

/-- The Belyi ratio r = m/(m+n) lies in (0,1) (matches the ScaleOrdering parameter
r = alpha1/alpha2 of the g-choice). -/
theorem belyi_rho_unit {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    0 < (m : ℚ) / (m + n) ∧ (m : ℚ) / (m + n) < 1 := by
  have h : (0 : ℚ) < m + n := by positivity
  constructor
  · exact div_pos (by exact_mod_cast hm) h
  · rw [div_lt_one h]
    exact_mod_cast Nat.lt_add_of_pos_right hn

/-- Bridge rows: (Belyi component, Lean evidence, status). -/
def mzk1BelyiRows : List (String × String × String) :=
  [ ("B_{m,n} vanishes at 0 and 1", "belyi_eval_zero / belyi_eval_one (canonical TauCeti Belyi, COMPLETE)", "PROVED (reuse)"),
    ("nonconstancy 0 < natDegree B_{m,n}", "belyi_natDegree_pos", "PROVED (reuse)"),
    ("STEP card collapse via canonical Belyi polynomial", "belyi_card_collapse (uses lemma22Step_card_lt)", "PROVED"),
    ("critical values of B_{m,n} in {0,1}", "belyi_criticalValues_subset (canonical TauCeti CriticalValues/Belyi)", "PROVED (reuse)"),
    ("Belyification existence", "belyi_exists_polynomial_aeval / belyi_exists_polynomial_eval (canonical; Mzk1 Lemma 2.2/2.4/GeometricCore)", "PROVED (reuse)"),
    ("Belyi ratio in (0,1)", "belyi_rho_unit (matches ScaleOrdering r = alpha1/alpha2)", "PROVED (reuse)"),
    ("paper-level Lemma 2.1/2.2/Thm 2.5", "still stage4/stepxi layered statements (no closure claim)", "OPEN (as before)") ]

theorem mzk1BelyiRows_length : mzk1BelyiRows.length = 7 := rfl

/-- Canonical port evidence (data): qpilot quickport root and file hashes. -/
def mzk1BelyiPortRefs : List (String × String) :=
  [ ("port root", "tmp/external/ported/tauceti_belyi_core (Apache-2.0 attribution retained)"),
    ("CriticalValues", "TauCeti/Algebra/Polynomial/CriticalValues.lean EXIT=0 SIZE 10151; sha256 6D3B5143…; CITABLE 13 decls"),
    ("Belyi", "TauCeti/Algebra/Polynomial/Belyi.lean EXIT=0 SIZE 19283; sha256 9948742A…; CITABLE 13 decls"),
    ("AbcConjecture", "TauCeti/NumberTheory/AbcConjecture.lean EXIT=0 SIZE 14080; sha256 B6336589…; CITABLE 8 decls (mainline AbcStatementAlignment consumer)"),
    ("corpus refs", "[Mzk1] Lemma 2.1 ~35-105; Lemma 2.2 106-135; Thm 2.5 207-221/222-281") ]

end LeanFormal.IUT.XiFPaper.Mzk1BelyiCanonicalActual

end
