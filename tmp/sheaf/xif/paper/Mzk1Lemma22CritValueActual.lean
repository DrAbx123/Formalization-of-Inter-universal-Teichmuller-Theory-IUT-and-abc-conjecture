import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1GDerivAevalActual
import tmp.sheaf.xif.paper.Mzk1GCriticalPointCasesActual
import tmp.sheaf.xif.paper.Mzk1BelyiCvBridgeActual

/-! # Mzk1Lemma22CritValueActual — C-point critical-value-in-image: statement + proved parts

STEP 0 prior-art: reuse Mzk1GChoiceUnramifiedActual (gPoly_derivative_eval over Q,
gPoly_eval_zero/alpha2, lam_mul_alpha1, lam_ne_zero'), Mzk1Lemma21Actual
(belyi21_derivative_root over C), Mzk1Lemma22GChoiceConstructActual (gPoly/fq/f0q),
RestatedLemma24InterfaceActual (polyEvalP1).  This file is the minimal-green staging
for the required item (i): the C-point critical-value-in-image statement is DEFINED and
the basic aeval/eval bridge is PROVED; the root-case proof is recorded as the named
statement CritValueInImageStatement (blocker rows below).  No fake, no sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GDerivAevalActual
open LeanFormal.IUT.XiFPaper.Mzk1GCriticalPointCasesActual
open LeanFormal.IUT.XiFPaper.Mzk1BelyiCvBridgeActual

/-- aeval of a Q-polynomial at a cast rational equals the cast of its eval (PROVED). -/
theorem aeval_cast_eval (f : ℚ[X]) (x : ℚ) :
    Polynomial.aeval ((x : ℚ) : ℂ) f = ((f.eval x : ℚ) : ℂ) := by
  have h : ((x : ℚ) : ℂ) = algebraMap ℚ ℂ x := rfl
  rw [h, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rfl

/-- **NAMED STATEMENT (item i, remaining proof):** every critical point z over C of the
g-choice polynomial gPoly D has its value equal to the value of gPoly at a point p of
the source S (and that value is rational, being one of f0q, f0q, fq m n r + f0q at
p = 0, alpha2, alpha1 respectively).  This is exactly what makes the composite
h.comp g satisfy the C-point unramifiedness condition for the restated 2.2 target. -/
def CritValueInImageStatement : Prop :=
  ∀ (D : Mzk1ScaleData) (_H : Lemma22Hypotheses D.S D.beta) (z : ℂ),
    Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 →
    ∃ p ∈ D.S, ∃ v : ℚ,
      (v : ℂ) = Polynomial.aeval z (gPoly D) ∧
      polyEvalP1 (gPoly D) p = P1Point.ofFinite v


/-- PROOF of the C-point critical-value-in-image statement (item (i)): the critical points
over C of gPoly are 0, alpha2, alpha1 (gPoly_critical_point_cases), and at those points the
values are f0q, f0q, fq m n r + f0q respectively, all realized at rational points of S. -/
theorem critValueInImage_proof : CritValueInImageStatement := by
  intro D H z hz
  rcases gPoly_critical_point_cases D hz with hz0 | hz2 | hz1
  · subst hz0
    refine ⟨P1Point.ofFinite (0 : ℚ), H.1, f0q D, ?_, ?_⟩
    · have h0c : (0 : ℂ) = (((0 : ℚ)) : ℂ) := by norm_num
      rw [h0c, aeval_cast_eval, gPoly_eval_zero]
    · show polyEvalP1 (gPoly D) (P1Point.ofFinite (0:ℚ)) = P1Point.ofFinite (f0q D)
      rw [show polyEvalP1 (gPoly D) (P1Point.ofFinite (0:ℚ)) =
        P1Point.ofFinite ((gPoly D).eval 0) from rfl, gPoly_eval_zero]
  · subst hz2
    refine ⟨P1Point.ofFinite D.alpha2, D.halpha2S, f0q D, ?_, ?_⟩
    · rw [aeval_cast_eval, gPoly_eval_alpha2 D D.hlam_alpha2]
    · show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha2) = P1Point.ofFinite (f0q D)
      rw [show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha2) =
        P1Point.ofFinite ((gPoly D).eval D.alpha2) from rfl, gPoly_eval_alpha2 D D.hlam_alpha2]
  · subst hz1
    refine ⟨P1Point.ofFinite D.alpha1, D.halpha1S, fq D.m D.n D.r + f0q D, ?_, ?_⟩
    · rw [aeval_cast_eval, gPoly_eval, lam_mul_alpha1 D]
    · show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha1) =
        P1Point.ofFinite (fq D.m D.n D.r + f0q D)
      rw [show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha1) =
        P1Point.ofFinite ((gPoly D).eval D.alpha1) from rfl, gPoly_eval, lam_mul_alpha1 D]

/-- Rows: proved part + named remaining obligations for item (i). -/
def critValueRows : List (String × String × String) :=
  [ ("aeval/eval bridge at cast rationals", "PROVED", "aeval_cast_eval")
  , ("derivative-aeval formula for gPoly over C", "NAMED", "TODO: derivative_comp + aeval_comp; formula lam * aeval (lam z) (belyi derivative)")
  , ("root cases over C via belyi21_derivative_root", "NAMED", "TODO: lam z in {0,1,r} => z in {0, alpha2, alpha1}")
  , ("value identification at the three rational points", "NAMED", "TODO: gPoly_eval_zero/alpha2 + lam_mul_alpha1 + gPoly_eval")
  , ("final CritValueInImageStatement", "NAMED", "TODO: combine the three rows")
  ]

theorem critValueRows_length : critValueRows.length = 5 := rfl

#check aeval_cast_eval
#check CritValueInImageStatement
#check critValueRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual
end
