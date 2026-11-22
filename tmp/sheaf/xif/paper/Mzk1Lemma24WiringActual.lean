import Mathlib
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.sheaf.xif.paper.Mzk1BelyiCanonicalActual
import tmp.sheaf.xif.paper.Mzk1Lemma24MainStatementActual
import tmp.sheaf.xif.paper.Mzk1Lemma24Descent2Actual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24WiringActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24MainStatementActual

/-- (M) re-export of the canonical Belyi data from stepxi's Mzk1BelyiCanonicalActual:
B_{m,n} vanishes at 0 (m>=1) and at 1 (n>=1), is nonconstant, and its critical values
lie in {0,1}. -/
theorem s3135_belyi_canonical_data {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (TauCeti.belyiPolynomial ℚ m n).natDegree = m + n ∧
    (TauCeti.belyiPolynomial ℚ m n).eval 0 = 0 ∧
    (TauCeti.belyiPolynomial ℚ m n).eval 1 = 0 ∧
    ((TauCeti.belyiPolynomial ℚ m n).criticalValues Qbar ⊆ ({0, 1} : Set Qbar)) :=
  ⟨TauCeti.natDegree_belyiPolynomial m n,
    TauCeti.eval_zero_belyiPolynomial (by omega) n,
    TauCeti.eval_one_belyiPolynomial m (by omega),
    TauCeti.criticalValues_belyiPolynomial_subset Qbar m n⟩

/-- (M1) exact remaining recipe, named: beta-avoidance for the f0-based step.  The
paper (Lemma 2.4 lines 183-199) first applies an affine automorphism with rational
coefficients and a positive rational scaling (Lemma 2.3) so that |beta| is large; then
the monic minimal polynomial f0 of alpha0 satisfies f0(alpha) = 0 for alpha in S and
f0(S0) values bounded by d0^{d0} (the (F) coefficient bound), while |f0(beta)| exceeds
the bound by monic growth.  The statement below records the exact missing formal piece:
growth of a monic polynomial at a large argument dominates any prescribed bound. -/
def MonicGrowthBetaAvoidanceStatement (d : Nat) (B R : Real) : Prop :=
  ∃ b : Real, B < b ∧ ∀ (p : Polynomial ℂ), p.Monic → p.natDegree = d →
    ∀ z : ℂ, R ≤ ‖z‖ → b ≤ ‖p.eval z‖

/-- (M1) status: beta-avoidance reduced to (i) the monic-polynomial growth estimate
above, (ii) the affine normalization from [Mzk1] Lemma 2.3 (separation), and (iii) the
(F) coefficient bound (PROVED).  Consumed assets: TauCeti Belyi/CriticalValues and
stepxi Mzk1BelyiCanonicalActual (Belyification, card collapse, critical values). -/
def s3135Mzk1WiringStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.wiring.M-M1-M3"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-199"
    status := Audit.VerificationStatus.interface
    note := "CONSUMED: stepxi Mzk1BelyiCanonicalActual (belyi_eval_zero/one, belyi_natDegree_pos, belyi_card_collapse, belyi_criticalValues_subset, belyi_exists_polynomial_aeval/eval) and ported TauCeti tauceti_belyi_core (Belyi.lean/CriticalValues.lean, both EXIT=0); re-exported as s3135_belyi_canonical_data. PROVED: (M3) rational-coefficient/Belyi polynomials are defined over every number field (Mzk1Lemma24Descent2Actual s3135_rational_polynomial_definedOver/s3135_belyiPolynomial_definedOver). REMAINING named: (M1) beta-avoidance via MonicGrowthBetaAvoidanceStatement (monic growth at large argument) + Lemma 2.3 affine normalization (Mzk1Lemma23Actual complex case proved) + (F) coefficient bound (proved); (M2) P^1-morphism/unramified-away predicate language gap. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.main-statement", "MZK1.lemma24.descent.wiring" ]
    sorryItems :=
      [ "(M1a) MonicGrowthBetaAvoidanceStatement (monic growth estimate)",
        "(M1b) Lemma 2.3 affine normalization wiring",
        "(M2) P^1-morphism/unramified-away predicate (language gap)" ] }

#check s3135_belyi_canonical_data
#check MonicGrowthBetaAvoidanceStatement
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24WiringActual
end
