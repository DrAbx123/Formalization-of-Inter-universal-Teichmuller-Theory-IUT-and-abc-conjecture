/-! # Mzk1ProvabilityClassificationActual — [Mzk1] provability classification summary

PAPER: Mochizuki, Noncritical Belyi Maps (corpus:
papers/motizuki_corpus/text/Noncritical Belyi Maps.txt).
Classification of every statement into (i) PROVABLE NOW (elementary, class A),
(ii) PROVABLE WITH EFFORT (reduction skeleton + algebraic infrastructure), (iii) DEEP
PAPER-INPUT (class B: needs geometric/analytic inputs not in the tree).

PRIOR ART (STEP 0): S3131Mzk1StatementActual; no LeanFormal Belyi-map / Q-scheme
curve infrastructure; Mathlib has polynomial/real-analysis basics for the elementary
lemmas but no Belyi maps.

LABEL: classification (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ProvabilityClassificationActual

structure Mzk1ClassificationRow where
  label : String
  classification : String
  infrastructureNeeded : String
  nextAction : String

def mzk1Classification : List Mzk1ClassificationRow :=
  [ ⟨"Def 1.1", "DEFINITION-DATA", "scheme morphisms over Q, unramifiedness over open complement, Belyi open; no Belyi infra in tree", "state as a data structure (dominant morphism + unramified over U_P); no proof needed"⟩,
    ⟨"Cor 1.2", "DEEP PAPER-INPUT", "Theorem 2.5 + Zariski base argument", "paper-input statement; formalization after Thm 2.5 statement layer"⟩,
    ⟨"Lemma 2.1", "PROVABLE NOW (class A)", "polynomials over Q, real inequalities, derivative; Mathlib polynomial/derivative support", "formalize directly: f(x)=x^m(x-1)^n, compute f', prove (a)-(d) as inequality/root facts"⟩,
    ⟨"Lemma 2.2", "PROVABLE (class A)", "Lemma 2.1 + induction on |S|, rational polynomial construction", "formalize induction; needs polynomial-map convention (morphism of P^1 via homogeneous coordinates)"⟩,
    ⟨"Lemma 2.3", "PROVABLE NOW (class A)", "complex metric, choice of lambda near beta; rational choice when beta rational", "formalize with Complex metric + Archimedean estimates"⟩,
    ⟨"Lemma 2.4", "PROVABLE WITH EFFORT (class A/B)", "algebraic numbers, Galois conjugates, minimal polynomials, reduced degree induction", "formalize using Mathlib algebraic closure/polynomial minimal polynomial API"⟩,
    ⟨"Thm 2.5", "DEEP (class B paper-input)", "smooth proper curves, Riemann-Roch/Serre duality, line bundles, basepoint-free linear systems, Frobenius/descent", "statement layer first (data record with the four properties); core geometric proof as formalization target"⟩,
    ⟨"Cor 3.1", "DEEP CONSEQUENCE (class B given Thm 2.5)", "Thm 2.5 + Zariski quasi-compactness/product space covering", "statement layer; reduction proof after Thm 2.5"⟩,
    ⟨"Cor 3.2", "DEEP CONSEQUENCE (class B given Thm 2.5)", "Thm 2.5 + local fields/product topologies/compactness", "statement layer; reduction proof after Thm 2.5"⟩ ]

theorem mzk1Classification_length : mzk1Classification.length = 9 := rfl

theorem mzk1Classification_length_check : mzk1Classification.length = 9 := rfl

#check mzk1Classification
#check mzk1Classification_length_check

end LeanFormal.IUT.XiFPaper.Mzk1ProvabilityClassificationActual