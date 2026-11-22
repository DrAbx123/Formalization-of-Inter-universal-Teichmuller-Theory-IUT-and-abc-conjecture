import tmp.sheaf.xif.paper.S2764FiveTorsionCriterionActual
import tmp.sheaf.xif.paper.S1405TorsionCardinalityPortActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual

noncomputable section
open WeierstrassCurve
open WeierstrassCurve.Affine
open Polynomial
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2768FiveTorsionCardActual

open LeanFormal.IUT.XiFPaper.S2764FiveTorsionCriterionActual
open LeanFormal.IUT.XiFPaper.S1405TorsionCardinalityPortActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- prePsi_5 has degree 12 (odd case of Mathlib natDegree_preΨ). -/
theorem S2768_prePsi5_natDegree :
    (W.preΨ (5 : ℤ)).natDegree = 12 := by
  rw [WeierstrassCurve.natDegree_preΨ (W := W) (by norm_num : ((5 : ℤ) : K) ≠ 0)]
  norm_num

/-- prePsi_5 has 12 distinct roots over an algebraically closed field. -/
theorem S2768_prePsi5_roots_card
    (hsep : (W.preΨ (5 : ℤ)).Separable) :
    (W.preΨ (5 : ℤ)).roots.toFinset.card = 12 := by
  classical
  have hpre : W.preΨ (5 : ℤ) ≠ 0 := by
    intro h
    have hdeg := S2768_prePsi5_natDegree W
    rw [h, natDegree_zero] at hdeg
    norm_num at hdeg
  have hsplit : (W.preΨ (5 : ℤ)).Splits := IsAlgClosed.splits _
  have hnodup : (W.preΨ (5 : ℤ)).roots.Nodup :=
    (Polynomial.nodup_roots_iff_of_splits hpre hsplit).mpr hsep
  rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots]
  exact S2768_prePsi5_natDegree W

#check S2768_prePsi5_natDegree
#check S2768_prePsi5_roots_card


/-- The S2764 affine criterion extends to all affine points, giving the
S1329 division criterion at n=5. -/
theorem S2768_fiveCriterion :
    LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual.s1329DivisionCriterion W 5 := by
  intro P
  rcases P with _ | ⟨x, y, hns⟩
  · rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_zero]
    simp only [eval_zero, iff_true]
    exact zsmul_zero (5 : ℤ)
  · rw [natCast_zsmul]
    rw [S2764_five_smul_eq_zero_iff_prePsi W hns]
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some]
    change eval x (W.preΨ (5 : ℤ)) = 0 ↔
      W.evalDivisionPolynomial x y (5 : ℤ) = 0
    rw [W.evalDivisionPolynomial_eq_eval_preΨ_of_odd (n := (5 : ℤ)) hns.1
      (by norm_num : ¬ Even (5 : ℤ))]

#check S2768_fiveCriterion

/-- Automatic root count: separability is supplied by S1942. -/
theorem S2768_prePsi5_roots_card_auto :
    (W.preΨ (5 : ℤ)).roots.toFinset.card = 12 :=
  S2768_prePsi5_roots_card W (S1942_preΨ_five_separable W)

/-- E[5] has cardinality 25 over the algebraic closure, from the S2764
criterion and S1942 separability. -/
theorem S2768_fiveTorsion_card :
    Nat.card (AddSubgroup.torsionBy (WeierstrassCurve.Affine.Point W) (5 : ℤ)) = 25 := by
  have hcrit : LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual.s1329DivisionCriterion W 5 :=
    S2768_fiveCriterion W
  have hsep : (W.preΨ (5 : ℤ)).Separable := S1942_preΨ_five_separable W
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0)
  have h5 : (5 : K) ≠ 0 := by exact_mod_cast (by norm_num : (5 : ℕ) ≠ 0)
  have h := natCard_torsionBy_eq_sq_of_criterion_and_separable
    (W := W) (l := 5) (by norm_num) h2 h5 hcrit hsep
  norm_num at h
  exact h

#check S2768_prePsi5_roots_card_auto
#check S2768_fiveTorsion_card
end LeanFormal.IUT.XiFPaper.S2768FiveTorsionCardActual
end