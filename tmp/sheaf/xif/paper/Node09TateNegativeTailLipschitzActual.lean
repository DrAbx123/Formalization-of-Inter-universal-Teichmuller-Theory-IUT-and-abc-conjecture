import tmp.sheaf.xif.paper.Mzk1P1NegativeTailActual
import tmp.sheaf.xif.paper.Node09TateTailLipschitzActual

noncomputable section
open LeanFormal.IUT
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Node09TateNegativeTailLipschitzActual

universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

open RigidTate in
theorem xNegativeTail_lipschitz
    (P : RigidTate.Parameter (K := K))
    (u v : RigidTate.FundamentalDomain P) :
    ‖(∑' n : ℕ, RigidTate.xNegativeTerm P v n) -
        (∑' n : ℕ, RigidTate.xNegativeTerm P u n)‖ ≤
      (‖P.q‖ / (1 - ‖P.q‖)) *
        (‖v.1 - u.1‖ / (‖u.1‖ * ‖v.1‖)) := by
  have hU : Summable (fun n : ℕ => RigidTate.xNegativeTerm P u n) :=
    RigidTate.Term.xNegativeTerm_summable P u
  have hV : Summable (fun n : ℕ => RigidTate.xNegativeTerm P v n) :=
    RigidTate.Term.xNegativeTerm_summable P v
  have hdiff : (∑' n : ℕ, RigidTate.xNegativeTerm P v n) -
      (∑' n : ℕ, RigidTate.xNegativeTerm P u n) =
      ∑' n : ℕ, (RigidTate.xNegativeTerm P v n - RigidTate.xNegativeTerm P u n) := by
    rw [hV.tsum_sub hU]
  rw [hdiff]
  have hq : ‖P.q‖ < 1 := P.q_norm_lt_one
  have hqR : ‖(‖P.q‖ : ℝ)‖ < 1 := by simpa using hq
  have hgeom : HasSum (fun n : ℕ => ‖P.q‖ ^ n) (1 - ‖P.q‖)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hqR
  have hshift0 : HasSum (fun n : ℕ => ‖P.q‖ * ‖P.q‖ ^ n)
      (‖P.q‖ * (1 - ‖P.q‖)⁻¹) := hgeom.mul_left ‖P.q‖
  have hshift1 : HasSum (fun n : ℕ => ‖P.q‖ ^ (n + 1))
      (‖P.q‖ * (1 - ‖P.q‖)⁻¹) := by
    simpa [pow_succ, mul_comm] using hshift0
  have hshift : HasSum (fun n : ℕ =>
      (‖v.1 - u.1‖ / (‖u.1‖ * ‖v.1‖)) * ‖P.q‖ ^ (n + 1))
      ((‖P.q‖ / (1 - ‖P.q‖)) * (‖v.1 - u.1‖ / (‖u.1‖ * ‖v.1‖))) := by
    have h := hshift1.mul_left (‖v.1 - u.1‖ / (‖u.1‖ * ‖v.1‖))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  refine tsum_of_norm_bounded hshift ?_
  intro n
  have hd := Mzk1P1NegativeTailActual.xNegativeTerm_diff_norm_le P u v n
  calc ‖RigidTate.xNegativeTerm P v n - RigidTate.xNegativeTerm P u n‖
      = ‖RigidTate.xNegativeTerm P u n - RigidTate.xNegativeTerm P v n‖ :=
          norm_sub_rev _ _
    _ ≤ (‖P.q‖ ^ (n + 1 : ℤ) / (‖u.1‖ * ‖v.1‖)) * ‖u.1 - v.1‖ := hd
    _ = (‖v.1 - u.1‖ / (‖u.1‖ * ‖v.1‖)) * ‖P.q‖ ^ (n + 1) := by
        have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [norm_sub_rev, hcast, zpow_natCast]
        field_simp


open RigidTate in
theorem xRemainder_lipschitz
    (P : RigidTate.Parameter (K := K))
    (u v : RigidTate.FundamentalDomain P) :
    ‖((∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) +
        RigidTate.xNegativeSeries P v) -
      ((∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) +
        RigidTate.xNegativeSeries P u)‖ ≤
      max (‖P.q‖ / (1 - ‖P.q‖))
          ((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖ := by
  have hT := Node09TateTailLipschitzActual.xPositiveTail_lipschitz P u v
  have hN := xNegativeTail_lipschitz P u v
  have hsplit : ((∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) +
      RigidTate.xNegativeSeries P v) -
      ((∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) +
        RigidTate.xNegativeSeries P u) =
      ((∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) -
        (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1))) +
      (RigidTate.xNegativeSeries P v - RigidTate.xNegativeSeries P u) := by ring
  rw [hsplit]
  have h1 : ‖(∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) -
      (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1))‖ ≤
      (‖P.q‖ / (1 - ‖P.q‖)) * ‖v.1 - u.1‖ := hT
  have h2 : ‖RigidTate.xNegativeSeries P v - RigidTate.xNegativeSeries P u‖ ≤
      ((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖ := by
    have := hN
    rw [RigidTate.xNegativeSeries] at *
    calc ‖(∑' n : ℕ, RigidTate.xNegativeTerm P v n) -
        (∑' n : ℕ, RigidTate.xNegativeTerm P u n)‖
        ≤ (‖P.q‖ / (1 - ‖P.q‖)) *
          (‖v.1 - u.1‖ / (‖u.1‖ * ‖v.1‖)) := this
      _ = ((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖ := by
          field_simp
  calc ‖(∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) -
      (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) +
      (RigidTate.xNegativeSeries P v - RigidTate.xNegativeSeries P u)‖
      ≤ max (‖(∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) -
          (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1))‖)
        ‖RigidTate.xNegativeSeries P v - RigidTate.xNegativeSeries P u‖ :=
          IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max ((‖P.q‖ / (1 - ‖P.q‖)) * ‖v.1 - u.1‖)
        (((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖) :=
          max_le_max h1 h2
    _ = max (‖P.q‖ / (1 - ‖P.q‖))
        ((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖ := by
          rw [max_mul_of_nonneg _ _ (norm_nonneg _)]

def Node09TateNegativeTailStatus : List String :=
  [ "actual: xNegativeTail_lipschitz sums the negative terms; donor Mzk1P1NegativeTailActual.xNegativeTerm_diff_norm_le has the decaying bound q^(n+1)/(||u|| ||v||)*||u-v||",
    "actual: xRemainder_lipschitz combines positive and negative halves by the nonarchimedean triangle inequality",
    "remaining: instantiate the Newton map hTmaps/hTcontract from this local Lipschitz bound",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateNegativeTailLipschitzActual