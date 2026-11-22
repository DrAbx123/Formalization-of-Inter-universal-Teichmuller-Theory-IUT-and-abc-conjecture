import tmp.sheaf.xif.paper.Node09TateNewtonPolygonActual
import LeanFormal.IUT.Foundations.Geometry.RigidTateSeries

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateRemainderLipschitzActual

universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

namespace RigidTate

/-- Algebraic difference formula for the positive X-term kernel. -/
theorem xPositiveTerm_sub_eq (P : RigidTate.Parameter (K := K))
    (u v : RigidTate.FundamentalDomain P) (n : ℕ) :
    RigidTate.xPositiveTerm P v n - RigidTate.xPositiveTerm P u n =
      (RigidTate.positiveArgument P v n - RigidTate.positiveArgument P u n) *
        (1 - RigidTate.positiveArgument P v n * RigidTate.positiveArgument P u n) /
        ((1 - RigidTate.positiveArgument P v n) ^ 2 *
          (1 - RigidTate.positiveArgument P u n) ^ 2) := by
  have hv : 1 - RigidTate.positiveArgument P v n ≠ 0 :=
    RigidTate.Argument.positiveArgument_denominator_ne_zero P v n
  have hu : 1 - RigidTate.positiveArgument P u n ≠ 0 :=
    RigidTate.Argument.positiveArgument_denominator_ne_zero P u n
  unfold RigidTate.xPositiveTerm
  field_simp [hv, hu]
  ring

/-- Termwise Lipschitz bound for the positive X-terms. -/
theorem xPositiveTerm_dist_le (P : RigidTate.Parameter (K := K))
    (u v : RigidTate.FundamentalDomain P) (n : ℕ) :
    ‖RigidTate.xPositiveTerm P v n - RigidTate.xPositiveTerm P u n‖ ≤
      ‖P.q‖ ^ (n : ℤ) * ‖v.val - u.val‖ := by
  have hzv : (1 : K) - RigidTate.positiveArgument P v n ≠ 0 :=
    RigidTate.Argument.positiveArgument_denominator_ne_zero P v n
  have hzu : (1 : K) - RigidTate.positiveArgument P u n ≠ 0 :=
    RigidTate.Argument.positiveArgument_denominator_ne_zero P u n
  have hzvnorm : ‖(1 : K) - RigidTate.positiveArgument P v n‖ = 1 :=
    RigidTate.Argument.positiveArgument_sub_one_norm P v n
  have hzunorm : ‖(1 : K) - RigidTate.positiveArgument P u n‖ = 1 :=
    RigidTate.Argument.positiveArgument_sub_one_norm P u n
  have hnum : ‖(1 : K) - RigidTate.positiveArgument P v n *
      RigidTate.positiveArgument P u n‖ ≤ 1 := by
    calc ‖(1 : K) - RigidTate.positiveArgument P v n *
        RigidTate.positiveArgument P u n‖
        ≤ max ‖(1 : K)‖ ‖RigidTate.positiveArgument P v n *
            RigidTate.positiveArgument P u n‖ := by
          simpa [sub_eq_add_neg] using
            IsUltrametricDist.norm_add_le_max (1 : K)
              (-(RigidTate.positiveArgument P v n * RigidTate.positiveArgument P u n))
      _ ≤ 1 := by
          apply max_le
          · norm_num
          · rw [norm_mul]
            exact mul_le_one₀
              (RigidTate.Argument.positiveArgument_norm_lt_one P v n).le
              (norm_nonneg _)
              (RigidTate.Argument.positiveArgument_norm_lt_one P u n).le
  rw [xPositiveTerm_sub_eq P u v n]
  simp only [norm_div, norm_mul, norm_pow, hzvnorm, hzunorm]
  norm_num
  have hdiff : ‖RigidTate.positiveArgument P v n -
      RigidTate.positiveArgument P u n‖ = ‖P.q‖ ^ (n : ℤ) * ‖v.val - u.val‖ := by
    rw [RigidTate.positiveArgument, RigidTate.positiveArgument, ← mul_sub, norm_mul,
      RigidTate.Parameter.norm_q_zpow]
  rw [hdiff]
  have hle : ‖(1 : K) - RigidTate.positiveArgument P v n *
      RigidTate.positiveArgument P u n‖ ≤ 1 := hnum
  calc ‖P.q‖ ^ (n : ℤ) * ‖v.val - u.val‖ *
      ‖(1 : K) - RigidTate.positiveArgument P v n *
        RigidTate.positiveArgument P u n‖
      ≤ ‖P.q‖ ^ (n : ℤ) * ‖v.val - u.val‖ * 1 :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ‖P.q‖ ^ (n : ℤ) * ‖v.val - u.val‖ := by ring

end RigidTate

def Node09TateRemainderLipschitzStatus : List String :=
  [ "actual: xPositiveTerm_sub_eq gives the exact difference formula for the positive X terms",
    "actual: xPositiveTerm_dist_le gives the termwise Lipschitz bound ||term(v)-term(u)|| <= ||q||^n * ||v-u|| on the rigid fundamental domain",
    "actual: negative-half bound now proved downstream (Node09TateNegativeTailLipschitzActual.xNegativeTail_lipschitz / xRemainder_lipschitz); the negative term bound is decaying q^(n+1) and summable",
    "remaining: instantiate Newton map hTmaps/hTcontract from the combined local Lipschitz bound",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateRemainderLipschitzActual