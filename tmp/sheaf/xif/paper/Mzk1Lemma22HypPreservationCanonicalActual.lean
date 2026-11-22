import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationSeparationActual
import tmp.sheaf.xif.paper.Mzk1BelyiCanonicalActual
import tmp.sheaf.xif.paper.Mzk1GChoiceCardActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: H-preservation|separation|canonical Belyi|gPoly -> hits Mzk1Lemma22HypPreservationActual (rows 1-5 PROVED), Mzk1Lemma22HypPreservationSeparationActual:76 hyp_separation (PROVED: separation for the reduced pair), Mzk1BelyiCanonicalActual (card collapse/Belyi assets), Mzk1GChoiceScaleActual (Lemma22Hypotheses) -> REUSE + ASSEMBLE.

# Mzk1Lemma22HypPreservationCanonicalActual — canonical-route H-preservation (FULL, separation included)

Corpus: Noncritical Belyi Maps.txt Lemma 2.2 (106-135); Lemma 2.1 (35-105).
CANONICAL ROUTE: reuse the stage4 g-choice layers (rows 1-5) + the PROVED separation
(Mzk1Lemma22HypPreservationSeparationActual.hyp_separation, canonical Belyi route) to
assemble the FULL H-preservation for the reduced pair (S' = g(S), beta' = g(beta)).
No fake; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationCanonicalActual

open Polynomial
open TauCeti
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationSeparationActual
open LeanFormal.IUT.XiFPaper.Mzk1BelyiCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceCardActual

/-- **FULL canonical H-preservation:** the reduced pair (g(S), g(beta)) satisfies
Lemma22Hypotheses, for even n, with all five components proved: 0/infinity
membership, positivity, beta-avoidance (stage4 rows), and separation (canonical
route, hyp_separation). -/
theorem canonical_hypotheses_preserved
    (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) (hne : Even D.n) :
    Lemma22Hypotheses (D.S.image (polyMapPoints (gPoly D)))
      (polyMapPoints (gPoly D) D.beta) := by
  refine ⟨target_zero_mem D H hne, target_infty_mem D H, target_positivity D H hne,
    ?_, hyp_separation D H hne⟩
  intro hmem
  exact target_beta_notin D H (by simpa using hmem)

/-- Canonical Belyi card collapse: if 0 and 1 lie in S then |B_{m,n}(S)| < |S|. -/
theorem canonical_card_collapse {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Finset (P1Point ℚ))
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (h1 : P1Point.ofFinite (1 : ℚ) ∈ S) :
    (S.image (polyMapPoints (belyiPolynomial ℚ m n))).card < S.card :=
  belyi_card_collapse hm hn S h0 h1

/-- Canonical-route rows (all five preservation components proved). -/
def canonicalHypPreservationRows : List (String × String × String) :=
  [ ("0 in reduced target image", "A", "REUSED stage4 target_zero_mem (PROVED)")
  , ("infinity in reduced target image", "A", "REUSED stage4 target_infty_mem (PROVED)")
  , ("positivity of reduced target points", "A", "REUSED stage4 target_positivity (PROVED)")
  , ("beta' not in reduced target image (avoids)", "A", "REUSED stage4 target_beta_notin (PROVED)")
  , ("beta'-separation (canonical route)", "A", "CONSUMED Mzk1Lemma22HypPreservationSeparationActual.hyp_separation (PROVED; lam_b_ge_two + fq bounds)")
  , ("canonical Belyi assets (card collapse, Belyification, critical values)", "A", "REUSED Mzk1BelyiCanonicalActual (ported FRESH)")
  , ("FULL Lemma22Hypotheses preservation", "A", "PROVED canonical_hypotheses_preserved") ]

/-- The canonical H-preservation row record has seven rows. -/
theorem canonicalHypPreservationRows_length : canonicalHypPreservationRows.length = 7 := rfl

#check canonical_hypotheses_preserved
#check canonical_card_collapse
#check canonicalHypPreservationRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationCanonicalActual
end