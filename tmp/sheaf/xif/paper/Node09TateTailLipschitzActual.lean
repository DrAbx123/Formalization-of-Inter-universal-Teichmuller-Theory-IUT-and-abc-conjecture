import tmp.sheaf.xif.paper.Node09TateRemainderLipschitzActual
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09TateRemainderLipschitzActual
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Node09TateTailLipschitzActual

universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

open RigidTate in
theorem xPositiveTail_lipschitz
    (P : RigidTate.Parameter (K := K))
    (u v : RigidTate.FundamentalDomain P) :
    ‖(∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) -
        (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1))‖ ≤
      (‖P.q‖ / (1 - ‖P.q‖)) * ‖v.1 - u.1‖ := by
  have hU : Summable (fun n : ℕ => RigidTate.xPositiveTerm P u (n + 1)) :=
    (summable_nat_add_iff 1).2 (RigidTate.Term.xPositiveTerm_summable P u)
  have hV : Summable (fun n : ℕ => RigidTate.xPositiveTerm P v (n + 1)) :=
    (summable_nat_add_iff 1).2 (RigidTate.Term.xPositiveTerm_summable P v)
  have hdiff : (∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) -
      (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) =
      ∑' n : ℕ, (RigidTate.xPositiveTerm P v (n + 1) -
        RigidTate.xPositiveTerm P u (n + 1)) := by
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
  have hshift : HasSum (fun n : ℕ => ‖v.1 - u.1‖ * ‖P.q‖ ^ (n + 1))
      ((‖P.q‖ / (1 - ‖P.q‖)) * ‖v.1 - u.1‖) := by
    have h := hshift1.mul_left ‖v.1 - u.1‖
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  refine tsum_of_norm_bounded hshift ?_
  intro n
  have hle := Node09TateRemainderLipschitzActual.RigidTate.xPositiveTerm_dist_le P u v (n + 1)
  have hz : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  rw [hz] at hle
  have hpow : ‖P.q‖ ^ ((n : ℤ) + 1) = ‖P.q‖ ^ (n + 1) := by
    have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, zpow_natCast]
  calc ‖RigidTate.xPositiveTerm P v (n + 1) - RigidTate.xPositiveTerm P u (n + 1)‖
      ≤ ‖P.q‖ ^ ((n : ℤ) + 1) * ‖v.1 - u.1‖ := hle
    _ = ‖v.1 - u.1‖ * ‖P.q‖ ^ (n + 1) := by rw [hpow]; ring

def Node09TateTailLipschitzStatus : List String :=
  [ "actual: xPositiveTail_lipschitz bounds the difference of the positive tails by (||q||/(1-||q||))*||v-u||",
    "remaining: the analogous negative-series summed Lipschitz bound, then hTcontract for the Newton map",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateTailLipschitzActual