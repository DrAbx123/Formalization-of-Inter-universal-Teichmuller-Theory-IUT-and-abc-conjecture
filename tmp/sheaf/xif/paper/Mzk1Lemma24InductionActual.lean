/-! # Mzk1Lemma24InductionActual — [Mzk1] Lemma 2.4 statement + induction plan

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4
lines 144-205; Mzk1Lemma22InductionActual (Lemma 2.2 plan); Mzk1Lemma23Actual
(separation PROVED finite complex case); no LeanFormal algebraic-number/Belyi-
descent infrastructure beyond Mathlib's IntermediateField/minpoly API.

PAPER (Lemma 2.4): finite S in P^1(Qbar) subset P^1(C), beta in Qbar minus S: there
exists nonconstant f in Qbar(x) defining phi with (a) phi(S) subset S_phi;
(b) phi(beta) in P^1(Qbar) minus S_phi; (c) phi unramified over P^1_Q minus S_phi;
moreover if S,beta are defined over a number field F then f may be taken in F(x).

FORMALIZATION STATUS (honest):
* Lemma 2.3 (separation via lambda near beta) PROVED finite complex case; rational
  lambda refinement MISSING.
* MISSING: the reduced-degree induction (paper: m(S) = max reduced degree, d(S);
  induction on (m(S),d(S)) via Galois-conjugate union and f0 normalization), and the
  P^1-morphism/descent language.

LABEL: statement layer + induction plan; proved:=false rows.  No fake proof. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24InductionActual

structure Mzk1Lemma24StatementRow where
  item : String
  status : String
  proved : Bool

def mzk1Lemma24Rows : List Mzk1Lemma24StatementRow :=
  [ ⟨"S finite in P^1(Qbar), beta in Qbar minus S", "HYPOTHESIS (data)", false⟩,
    ⟨"exists nonconstant f in Qbar(x) with phi(S) subset S_phi, phi(beta) outside S_phi, unramified over P^1 minus S_phi", "CONCLUSION; proof: reduced-degree induction on (m(S),d(S)) MISSING", false⟩,
    ⟨"descent: if S,beta defined over F then phi defined over F", "CONCLUSION; Galois-stability + descent MISSING", false⟩,
    ⟨"reduced degree m(S), d(S) definitions", "DEFINITIONS (paper); can be formalized with Mathlib minpoly/IntermediateField — NOT YET WRITTEN", false⟩,
    ⟨"induction step: replace S by Galois-conjugate union, apply f0 normalization, reduce (m,d)", "PROOF METHOD (paper lines 161-206); MISSING", false⟩ ]

theorem mzk1Lemma24Rows_length : mzk1Lemma24Rows.length = 5 := rfl

#check mzk1Lemma24Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24InductionActual