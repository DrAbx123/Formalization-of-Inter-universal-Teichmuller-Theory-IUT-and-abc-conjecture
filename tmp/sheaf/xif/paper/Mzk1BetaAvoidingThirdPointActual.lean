import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiRationalActual
import tmp.sheaf.xif.paper.Mzk1BetaAvoidingExteriorActual
import tmp.sheaf.xif.paper.Mzk1BadParamProofActual
import tmp.sheaf.xif.paper.Mzk1BelyiMaximizerActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

noncomputable section

open Polynomial TauCeti

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingThirdPointActual

open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiSmallActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiRationalActual
open LeanFormal.IUT.XiFPaper.Mzk1BadParamFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1BadParamProofActual
open LeanFormal.IUT.XiFPaper.Mzk1BelyiMaximizerActual

/-!
# Mzk1BetaAvoidingThirdPointActual — the corrected parametric beta-avoiding reduction
(third-point freedom + odd k)

## Context

Mzk1BetaAvoidingBelyiRationalActual isolates the whole remaining gap of the beta-avoiding
Belyi construction as the single named Prop BetaAvoidingStep, and proves that the canonical
TauCeti three-point step is *not* beta-avoiding (tauCetiStep_not_betaAvoiding: for
S = {0,1,3}, beta = 4 the forced ratio is 1/3 and B_{m,2m}(4/3) = 1 for every m).
Mzk1BetaAvoidingBelyiSmallActual and Mzk1BetaAvoidingExteriorActual close the *small*
case |S| <= 3 unconditionally (belyiBetaAvoidingSmallStatement_proved).

The present file executes the corrected plan (Hull): *third-point freedom* (after fixing
a = min S and b = max S, the remaining degree of freedom is the choice of the third point
c in S \ {a,b}, whose normalized image is the critical point of the Belyi polynomial),
*odd scaling* (B_{kp,kq}(u) = (B_{p,q}(u))^k), and the assembly of the beta-avoiding Belyi
construction from a step lemma for |S| >= 4 (the small case being already closed).

## Results of this file

* **STEP 1** (belyiEvalQ_odd_scale_ne_zero_one, belyiPolynomial_odd_scale_avoids): for
  u not in {0,1}, positive (p,q) with B_{p,q}(u) != 1 and **odd** k >= 1, one has
  B_{kp,kq}(u) = (B_{p,q}(u))^k not in {0,1}.
* div_add_scale: scaling (p,q) -> (kp,kq) does not move the critical-point ratio
  p/(p+q); exists_ratio_of_between: a point strictly between a and b always realises a
  ratio p/(p+q) with p,q > 0 -- the ratio bookkeeping of the plan is never the obstruction.
* **The step theorem** exists_card_image_lt_beta_of_third_point: given points a, b, c in S,
  positive (p,q) with (c-a)/(b-a) = p/(p+q), and the two *value conditions*
  B_{p,q}((beta-a)/(b-a)) != 1 and B_{p,q}((beta-a)/(b-a)) != B_{p,q}((s-a)/(b-a)) for all
  other s in S, the one-layer polynomial f = B_{p,q} o affineNorm a b has all the
  properties needed by the induction (CritIn01 f, |f(S)| < |S|, 0,1 in f(S),
  f(beta) not in f(S)).  exists_card_image_lt_beta_of_third_point_odd_scale is the same
  for the odd-scaled family (kp, kq).
* exists_card_image_lt_beta_of_third_point_sign and its two parity corollaries
  (exists_card_image_lt_beta_of_third_point_of_gt_odd, ..._of_lt_odd) close the *exterior*
  case for every |S| >= 4 whenever the selected third point has an odd Belyi denominator q
  (for beta > max S) or an odd numerator p (for beta < min S): the normalized beta then maps
  to a negative value, which excludes 0, 1 and the (0,1)-valued images of the other points.
  The residue of the exterior case is its parity-stuck part.
* interior_value_ne_one: for a < c < b and a < beta < b with beta != c, the first value
  condition holds **automatically** (maximizer uniqueness: B_{p,q}(u) = 1 with u in (0,1)
  forces u = p/(p+q) = (c-a)/(b-a), i.e. beta = c).
* ThirdPointClaim and **thirdPointClaim_false**: the plan's STEP 2 as literally stated
  (|S| >= 3, some third point c or orientation with B_{p_c,q_c}(u) != 1) is **FALSE**; the
  counterexample is S = {0,1,3}, beta = 4, where the only third point c = 1 gives the
  critical ratio 1/3 in the orientation 0 -> 0, 3 -> 1 and 2/3 in the reversed orientation
  3 -> 0, 0 -> 1, and B_{1,2}(4/3) = 1, B_{2,1}(-1/3) = 1
  (backward_orientation_value_eq_one for the reversed orientation).  Hence the step lemma
  can only be required for |S| >= 4, which is why the assembly below uses the proved
  |S| <= 3 base case instead of BetaAvoidingStep's |S| > 2.
* **Assembly** (exists_betaAvoiding_of_thirdPoint_step, exists_card_image_lt_beta,
  exists_betaAvoiding_of_thirdPoint_valueConditions): the beta-avoiding Belyi construction
  for every finite S subset of Q and every beta not in S follows from the third-point step
  for |S| >= 4 (i.e. from the named value conditions ThirdPointValueConditions), the base
  case |S| <= 3 being already proved.

## The precise remaining gap (blocker, stated exactly)

ThirdPointValueConditions (Section E) asks, for every S with 4 <= S.card and beta not in S,
for a third-point datum (a,b,c,p,q) satisfying the two value conditions of the step theorem.
It is **not proved here**.  The two conditions are genuinely needed:

* the *first* one fails when the normalized beta is an extra preimage of 1
  (S = {0,1,3}, beta = 4 above).  For an *interior* beta (strictly between the two
  normalization points) it can never fail (interior_value_ne_one); for |S| >= 4 there is at
  least a second candidate, which repairs such a failure in every instance I checked, but no
  proof is available;
* the *second* one (not considered by the plan at all) fails when the normalized beta is the
  "partner" of the normalized image of another point of S under the unimodal Belyi
  polynomial; e.g. S = {0, 1/4, 1/2, 1}, beta = 3/4: for c = 1/2 one has
  f = B_{1,1} o id, f(beta) = f(1/4) = 3/4, so that datum fails even though
  |f(S)| = 3 < 4 -- the candidate c = 1/4 (ratio 1/4, B_{1,3}(3/4) = 1/9) saves it.
  Odd scaling cannot repair it, because x -> x^k is injective and preserves the collision.

No sorry, no new axioms, no PUnit/True placeholders; #print axioms at the end.
-/

/-! ## Section A -- STEP 1: odd scaling -/

/-- **STEP 1 of the corrected plan.**  For fixed rational u not in {0,1}, positive (p,q) with
B_{p,q}(u) != 1, and **odd** k >= 1, the odd scaling (p,q) -> (kp,kq) gives
B_{kp,kq}(u) = (B_{p,q}(u))^k not in {0,1}: a negative value stays negative (k odd), a value
with |B| > 1 stays outside {0,1}, and (B_{p,q}(u))^k = 1 with odd k forces B_{p,q}(u) = 1;
B_{p,q}(u) = 0 is impossible because u is not in {0,1}. -/
theorem belyiEvalQ_odd_scale_ne_zero_one {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) {u : ℚ}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) {k : ℕ} (hk : Odd k) (hB : belyiEvalQ p q u ≠ 1) :
    belyiEvalQ (k * p) (k * q) u ≠ 0 ∧ belyiEvalQ (k * p) (k * q) u ≠ 1 := by
  have hB0 : belyiEvalQ p q u ≠ 0 := belyiEvalQ_ne_zero p q hp hq u hu0 hu1
  obtain ⟨t, ht⟩ := hk
  have hk0 : k ≠ 0 := by omega
  constructor
  · rw [belyiEvalQ_scaling]
    exact pow_ne_zero _ hB0
  · rw [belyiEvalQ_scaling]
    intro h
    rcases pow_eq_one_iff_cases.mp h with h1 | h1 | ⟨h1, h2⟩
    · exact hk0 h1
    · exact hB h1
    · obtain ⟨s, hs⟩ := h2
      omega

/-- The scaling identity of the Belyi family, in the belyiPolynomial form:
B_{kp,kq}(u) = (B_{p,q}(u))^k. -/
theorem eval_belyiPolynomial_scale (p q k : ℕ) (u : ℚ) :
    (belyiPolynomial ℚ (k * p) (k * q)).eval u = (belyiPolynomial ℚ p q).eval u ^ k :=
  belyiEvalQ_scaling p q u k

/-- **STEP 1 in polynomial form**: the odd-scaled Belyi polynomial avoids {0,1} at u. -/
theorem belyiPolynomial_odd_scale_avoids {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {u : ℚ}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) {k : ℕ} (hk : Odd k)
    (hB : (belyiPolynomial ℚ p q).eval u ≠ 1) :
    (belyiPolynomial ℚ (k * p) (k * q)).eval u ≠ 0 ∧
      (belyiPolynomial ℚ (k * p) (k * q)).eval u ≠ 1 :=
  belyiEvalQ_odd_scale_ne_zero_one hp.ne' hq.ne' hu0 hu1 hk hB

/-- **The critical-point ratio is invariant under scaling**: (kp)/(kp + kq) = p/(p+q) for
k != 0.  This is what makes the odd scaling legal for the third-point step: the normalized
third point stays the critical point of the scaled Belyi polynomial. -/
theorem div_add_scale {k : ℕ} (hk : k ≠ 0) (p q : ℕ) :
    ((k * p : ℕ) : ℚ) / (((k * p : ℕ) : ℚ) + ((k * q : ℕ) : ℚ)) =
      (p : ℚ) / ((p : ℚ) + q) := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have h1 : ((k * p : ℕ) : ℚ) = (k : ℚ) * (p : ℚ) := by push_cast; ring
  have h2 : ((k * q : ℕ) : ℚ) = (k : ℚ) * (q : ℚ) := by push_cast; ring
  rw [h1, h2, ← mul_add]
  exact mul_div_mul_left _ _ hkQ

/-- **Ratio realization is automatic.**  A rational point c strictly between a and b always
realises a critical-point ratio p/(p+q) with positive p, q; so the plan's "(m,n) ratio
m/(m+n) = r determines (p,q)" step is never an obstruction. -/
theorem exists_ratio_of_between {a b c : ℚ} (hac : a < c) (hcb : c < b) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q) := by
  have hba : (0 : ℚ) < b - a := by linarith
  have h1 : 0 < (c - a) / (b - a) := div_pos (by linarith) hba
  have h2 : (c - a) / (b - a) < 1 := by
    rw [div_lt_one hba]
    linarith
  obtain ⟨m, n, hm, hn, he⟩ := Rat.exists_eq_div_add_of_pos_of_lt_one h1 h2
  exact ⟨m, n, Nat.pos_of_ne_zero hm, Nat.pos_of_ne_zero hn, he⟩

/-! ## Section B -- the third-point step with beta tracking -/

/-- **The third-point step with beta tracking (one layer).**  Let a, b, c be points of S with
a != b, c != a, c != b, let p, q be positive integers whose critical-point ratio is the
normalized image of c, and assume the two **value conditions**

* B_{p,q}((beta-a)/(b-a)) != 1, and
* B_{p,q}((s-a)/(b-a)) != B_{p,q}((beta-a)/(b-a)) for every other s in S.

Then f = B_{p,q} o affineNorm a b is the beta-avoiding three-point step:
f has positive degree, CritIn01 f, f(a) = f(b) = 0 (so |f(S)| < |S|), f(c) = 1
(so 0, 1 in f(S)) and f(beta) is not in f(S).

Note that a, b need NOT be the minimum and maximum of S, and beta need NOT lie in [a,b];
only the two value conditions are used. -/
theorem exists_card_image_lt_beta_of_third_point
    {S : Finset ℚ} {β a b c : ℚ} {p q : ℕ}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hβS : β ∉ S)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hp : 0 < p) (hq : 0 < q)
    (hratio : (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q))
    (hV1 : (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1)
    (hV2 : ∀ s ∈ S, s ≠ a → s ≠ b → s ≠ c →
      (belyiPolynomial ℚ p q).eval ((s - a) / (b - a)) ≠
        (belyiPolynomial ℚ p q).eval ((β - a) / (b - a))) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := hq.ne'
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hfa : ((belyiPolynomial ℚ p q).comp (affineNorm a b)).eval a = 0 := by
    rw [eval_affineBelyi]
    have h0 : (a - a) / (b - a) = 0 := by rw [sub_self, zero_div]
    rw [h0]
    exact eval_zero_belyiPolynomial hp0 q
  have hfb : ((belyiPolynomial ℚ p q).comp (affineNorm a b)).eval b = 0 := by
    rw [eval_affineBelyi, div_self hba]
    exact eval_one_belyiPolynomial p hq0
  have hfc : ((belyiPolynomial ℚ p q).comp (affineNorm a b)).eval c = 1 := by
    rw [eval_affineBelyi, hratio]
    exact eval_div_belyiPolynomial (K := ℚ) p q
  have huβ0 : (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 0 := by
    intro h0
    rcases (eval_belyi_eq_zero_iff hp0 hq0 ((β - a) / (b - a))).mp h0 with h1 | h1
    · have h2 : β - a = 0 * (b - a) := (div_eq_iff hba).mp h1
      have h3 : β = a := by linarith
      exact hβS (by rw [h3]; exact haS)
    · have h2 : β - a = 1 * (b - a) := (div_eq_iff hba).mp h1
      have h3 : β = b := by linarith
      exact hβS (by rw [h3]; exact hbS)
  refine ⟨(belyiPolynomial ℚ p q).comp (affineNorm a b), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact affineBelyi_natDegree_pos hp hq hab
  · exact affineBelyi_critIn01 (by omega) (by omega) hab
  · refine lt_of_le_of_ne Finset.card_image_le ?_
    intro hcard
    have hinj := (Finset.card_image_iff.mp hcard) haS hbS
    exact hab (hinj (hfa.trans hfb.symm))
  · exact Finset.mem_image.mpr ⟨a, haS, hfa⟩
  · exact Finset.mem_image.mpr ⟨c, hcS, hfc⟩
  · intro hmem
    obtain ⟨s, hsS, hfs⟩ := Finset.mem_image.mp hmem
    have hβval : ((belyiPolynomial ℚ p q).comp (affineNorm a b)).eval β =
        (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) := eval_affineBelyi p q a b β
    have hsval : ((belyiPolynomial ℚ p q).comp (affineNorm a b)).eval s =
        (belyiPolynomial ℚ p q).eval ((s - a) / (b - a)) := eval_affineBelyi p q a b s
    rw [hβval, hsval] at hfs
    by_cases hsa : s = a
    · rw [hsa] at hfs
      simp only [sub_self, zero_div] at hfs
      rw [eval_zero_belyiPolynomial hp0 q] at hfs
      exact huβ0 hfs.symm
    · by_cases hsb : s = b
      · rw [hsb] at hfs
        rw [div_self hba, eval_one_belyiPolynomial p hq0] at hfs
        exact huβ0 hfs.symm
      · by_cases hsc : s = c
        · rw [hsc] at hfs
          rw [hratio, eval_div_belyiPolynomial] at hfs
          exact hV1 hfs.symm
        · exact hV2 s hsS hsa hsb hsc hfs

/-- **The odd-scaled third-point step.**  The same step, using the odd-scaled family
(kp, kq) instead of (p, q): the critical ratio is unchanged (div_add_scale), the first value
condition transfers through STEP 1 (belyiPolynomial_odd_scale_avoids) and the second through
the injectivity of x -> x^k for odd k.  This is the form in which the corrected plan wants to
use "odd k". -/
theorem exists_card_image_lt_beta_of_third_point_odd_scale
    {S : Finset ℚ} {β a b c : ℚ} {p q k : ℕ}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hβS : β ∉ S)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hp : 0 < p) (hq : 0 < q) (hk : Odd k)
    (hratio : (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q))
    (hV1 : (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1)
    (hV2 : ∀ s ∈ S, s ≠ a → s ≠ b → s ≠ c →
      (belyiPolynomial ℚ p q).eval ((s - a) / (b - a)) ≠
        (belyiPolynomial ℚ p q).eval ((β - a) / (b - a))) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hk0 : k ≠ 0 := by
    rcases hk with ⟨t, ht⟩
    omega
  have hu0 : (β - a) / (b - a) ≠ 0 := by
    intro h
    rcases div_eq_zero_iff.mp h with h1 | h1
    · have h3 : β = a := by linarith
      exact hβS (by rw [h3]; exact haS)
    · exact hba h1
  have hu1 : (β - a) / (b - a) ≠ 1 := by
    intro h
    have h1 : β - a = 1 * (b - a) := (div_eq_iff hba).mp h
    have h3 : β = b := by linarith
    exact hβS (by rw [h3]; exact hbS)
  have hV1' : (belyiPolynomial ℚ (k * p) (k * q)).eval ((β - a) / (b - a)) ≠ 1 :=
    (belyiPolynomial_odd_scale_avoids hp hq hu0 hu1 hk hV1).2
  have hV2' : ∀ s ∈ S, s ≠ a → s ≠ b → s ≠ c →
      (belyiPolynomial ℚ (k * p) (k * q)).eval ((s - a) / (b - a)) ≠
        (belyiPolynomial ℚ (k * p) (k * q)).eval ((β - a) / (b - a)) := by
    intro s hs h1 h2 h3 hcontra
    rw [eval_belyiPolynomial_scale, eval_belyiPolynomial_scale] at hcontra
    exact hV2 s hs h1 h2 h3 ((Odd.strictMono_pow hk).injective hcontra)
  refine exists_card_image_lt_beta_of_third_point haS hbS hcS hβS hab hca hcb ?_ ?_ ?_
    hV1' hV2'
  · exact Nat.mul_pos (Nat.pos_of_ne_zero hk0) hp
  · exact Nat.mul_pos (Nat.pos_of_ne_zero hk0) hq
  · rw [div_add_scale hk0]
    exact hratio


/-- **Sign version of the third-point step.**  If a and b are the minimum and the maximum of S
(so that every other normalized point lies in (0,1), where the Belyi polynomial takes values
in (0,1)) and the normalized value of beta lies strictly outside [0,1], then the second value
condition V2 is automatic: B_{p,q}((beta-a)/(b-a)) is outside (0,1) while every
B_{p,q}((s-a)/(b-a)) lies in (0,1).  So for exterior beta the step reduces to the single
scalar condition B != 1 plus a sign condition. -/
theorem exists_card_image_lt_beta_of_third_point_sign
    {S : Finset ℚ} {β a b c : ℚ} {p q : ℕ}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hβS : β ∉ S)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hmin : ∀ s ∈ S, a ≤ s) (hmax : ∀ s ∈ S, s ≤ b)
    (hp : 0 < p) (hq : 0 < q)
    (hratio : (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q))
    (hV1 : (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1)
    (hbound : (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) < 0 ∨
      1 < (belyiPolynomial ℚ p q).eval ((β - a) / (b - a))) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  have hba : (0 : ℚ) < b - a := by
    have h1 : a < b := lt_of_le_of_ne (hmin b hbS) hab
    linarith
  refine exists_card_image_lt_beta_of_third_point haS hbS hcS hβS hab hca hcb hp hq hratio
    hV1 ?_
  intro s hs hsa hsb hsc
  have has : a < s := lt_of_le_of_ne (hmin s hs) hsa.symm
  have hsb' : s < b := lt_of_le_of_ne (hmax s hs) hsb
  have hw0 : 0 < (s - a) / (b - a) := div_pos (by linarith) hba
  have hw1 : (s - a) / (b - a) < 1 := by
    rw [div_lt_one hba]
    linarith
  have hwne : (s - a) / (b - a) ≠ (p : ℚ) / ((p : ℚ) + q) := by
    intro h
    apply hsc
    have h1 : (s - a) / (b - a) = (c - a) / (b - a) := by
      rw [h, hratio]
    have h2 : (s - a) * (b - a) = (c - a) * (b - a) :=
      (div_eq_div_iff hba.ne' hba.ne').mp h1
    have h3 : s - a = c - a := mul_right_cancel₀ hba.ne' h2
    linarith
  have hpos : 0 < (belyiPolynomial ℚ p q).eval ((s - a) / (b - a)) :=
    eval_belyi_pos hp hq hw0 hw1
  have hlt : (belyiPolynomial ℚ p q).eval ((s - a) / (b - a)) < 1 :=
    eval_belyi_lt_one hp hq hw0 hw1 hwne
  rcases hbound with hb | hb <;> linarith

/-- **Exterior right case, parity-solvable: beta > max S and an odd Belyi denominator.**
If a = min S, b = max S, beta > b, and the critical point of the third point is p/(p+q) with
q odd, then the normalized value of beta is > 1 and B_{p,q} is negative there
(eval_belyi_neg_of_one_lt), so the sign version of the step applies.  This closes the
exterior case beta > max S for every |S| >= 4 whose selected third point has odd q. -/
theorem exists_card_image_lt_beta_of_third_point_of_gt_odd
    {S : Finset ℚ} {β a b c : ℚ} {p q : ℕ}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hβS : β ∉ S)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hmin : ∀ s ∈ S, a ≤ s) (hmax : ∀ s ∈ S, s ≤ b)
    (hp : 0 < p) (hq : 0 < q) (hqodd : Odd q) (hβb : b < β)
    (hratio : (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q)) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  have hba : (0 : ℚ) < b - a := by
    have h1 : a < b := lt_of_le_of_ne (hmin b hbS) hab
    linarith
  have hu : 1 < (β - a) / (b - a) := by
    rw [one_lt_div hba]
    linarith
  have hV1 : (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1 := by
    have hneg := eval_belyi_neg_of_one_lt hp hq hqodd hu
    linarith
  refine exists_card_image_lt_beta_of_third_point_sign haS hbS hcS hβS hab hca hcb hmin hmax
    hp hq hratio hV1 ?_
  exact Or.inl (eval_belyi_neg_of_one_lt hp hq hqodd hu)

/-- **Exterior left case, parity-solvable: beta < min S and an odd Belyi numerator.**
If a = min S, b = max S, beta < a, and the critical point of the third point is p/(p+q) with
p odd, then the normalized value of beta is < 0 and B_{p,q} is negative there
(eval_belyi_neg_of_lt_zero), so the sign version of the step applies. -/
theorem exists_card_image_lt_beta_of_third_point_of_lt_odd
    {S : Finset ℚ} {β a b c : ℚ} {p q : ℕ}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hβS : β ∉ S)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hmin : ∀ s ∈ S, a ≤ s) (hmax : ∀ s ∈ S, s ≤ b)
    (hp : 0 < p) (hq : 0 < q) (hpod : Odd p) (hβa : β < a)
    (hratio : (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q)) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  have hba : (0 : ℚ) < b - a := by
    have h1 : a < b := lt_of_le_of_ne (hmin b hbS) hab
    linarith
  have hu : (β - a) / (b - a) < 0 := div_neg_of_neg_of_pos (by linarith) hba
  have hV1 : (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1 := by
    have hneg := eval_belyi_neg_of_lt_zero hp hq hpod hu
    linarith
  refine exists_card_image_lt_beta_of_third_point_sign haS hbS hcS hβS hab hca hcb hmin hmax
    hp hq hratio hV1 ?_
  exact Or.inl (eval_belyi_neg_of_lt_zero hp hq hpod hu)

/-! ## Section C -- the interior case: the first value condition is automatic -/

/-- **Interior beta: the first value condition cannot fail.**  If a < c < b and a < beta < b
with beta != c, and p/(p+q) = (c-a)/(b-a), then B_{p,q}((beta-a)/(b-a)) != 1.  Indeed
u = (beta-a)/(b-a) lies in (0,1), so maximizer uniqueness forces u = p/(p+q), i.e.
beta = c, contradiction.  This disposes of the plan's "all-k-bad" worry whenever beta lies
strictly between the two normalization points. -/
theorem interior_value_ne_one {a b c β : ℚ} {p q : ℕ}
    (hab : a < b) (hac : a < c) (hcb : c < b) (hβa : a < β) (hβb : β < b) (hβc : β ≠ c)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hratio : (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q)) :
    (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1 := by
  have hba : (0 : ℚ) < b - a := by linarith
  have hu0 : 0 < (β - a) / (b - a) := div_pos (by linarith) hba
  have hu1 : (β - a) / (b - a) < 1 := by
    rw [div_lt_one hba]
    linarith
  intro h
  have hkey := (belyiPolynomial_eval_eq_one_iff p q hp hq ((β - a) / (b - a)) hu0 hu1).mp h
  have hsum : (0 : ℚ) < (p : ℚ) + q := by
    have h1 : (0 : ℚ) < (p : ℚ) := by
      have h1' : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
      linarith
    have h2 : (0 : ℚ) ≤ (q : ℚ) := by positivity
    linarith
  have hval : (β - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q) := by
    rw [eq_div_iff hsum.ne']
    push_cast at hkey
    linarith
  have h3 : (β - a) / (b - a) = (c - a) / (b - a) := by
    rw [hval, hratio]
  have h4 : (β - a) * (b - a) = (c - a) * (b - a) :=
    (div_eq_div_iff hba.ne' hba.ne').mp h3
  have h5 : β - a = c - a := mul_right_cancel₀ hba.ne' h4
  exact hβc (by linarith)

/-! ## Section D -- the plan's STEP 2 is false as stated (|S| >= 3) -/

/-- **The plan's STEP-2 candidate claim**, in the form that allows **both orientations**
(the pair (a, b) may be given in either order, and positive (p, q) encode the critical point
p/(p+q)).  This is the statement the corrected plan needs in order to choose the third
point: for every S with 3 <= S.card and every beta not in S, some third point c and some
positive (p, q) with the right critical ratio avoid the value 1 at the normalized beta. -/
def ThirdPointClaim : Prop :=
  ∀ (S : Finset ℚ) (β a b : ℚ), 3 ≤ S.card → β ∉ S → a ∈ S → b ∈ S →
    (∀ s ∈ S, min a b ≤ s ∧ s ≤ max a b) →
    ∃ (c : ℚ) (p q : ℕ), c ∈ S ∧ c ≠ a ∧ c ≠ b ∧ 0 < p ∧ 0 < q ∧
      (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q) ∧
      (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1

/-- The normalization pair (0, 3) of S = {0, 1, 3}: every point of S lies in [0, 3]. -/
theorem zero_three_bound :
    ∀ s ∈ ({0, 1, 3} : Finset ℚ), min (0 : ℚ) 3 ≤ s ∧ s ≤ max (0 : ℚ) 3 := by
  intro s hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;> norm_num

/-- **The forward orientation always hits the value 1** on S = {0, 1, 3}, beta = 4: the only
third point is c = 1, whose critical ratio is 1/3, and B_{p,2p}(4/3) = (B_{1,2}(4/3))^p = 1
for every p >= 1. -/
theorem forward_orientation_value_eq_one {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hratio : ((1 : ℚ) - 0) / (3 - 0) = (p : ℚ) / ((p : ℚ) + q)) :
    (belyiPolynomial ℚ p q).eval (((4 : ℚ) - 0) / (3 - 0)) = 1 := by
  have hr : (1 / 3 : ℚ) = (p : ℚ) / ((p : ℚ) + q) := by
    rw [← hratio]
    norm_num
  have hsum : ((p : ℚ) + q) ≠ 0 := by positivity
  have hqeq : (q : ℚ) = 2 * (p : ℚ) := by
    have hmul : (1 / 3 : ℚ) * ((p : ℚ) + q) = (p : ℚ) := by
      rw [hr]
      exact div_mul_cancel₀ _ hsum
    linarith
  have hq2 : q = 2 * p := by exact_mod_cast hqeq
  have h43 : (((4 : ℚ) - 0) / (3 - 0)) = 4 / 3 := by norm_num
  rw [h43, hq2]
  have hscale : (belyiPolynomial ℚ p (2 * p)).eval (4 / 3) =
      ((belyiPolynomial ℚ 1 2).eval (4 / 3)) ^ p := by
    have h := eval_belyiPolynomial_scale 1 2 p (4 / 3)
    rw [Nat.mul_one, Nat.mul_comm p 2] at h
    exact h
  rw [hscale, canonical_exterior_bad_point, one_pow]

/-- **The reversed orientation also always hits the value 1** on S = {0, 1, 3}, beta = 4:
mapping 3 -> 0 and 0 -> 1 gives the third point c = 1 critical ratio 2/3 and normalized
beta -1/3, and B_{2q,q}(-1/3) = (B_{2,1}(-1/3))^q = 1 for every q >= 1.  So the plan's
"endpoint swap / direction" fallback does not help at |S| = 3. -/
theorem backward_orientation_value_eq_one {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hratio : ((1 : ℚ) - 3) / (0 - 3) = (p : ℚ) / ((p : ℚ) + q)) :
    (belyiPolynomial ℚ p q).eval (((4 : ℚ) - 3) / (0 - 3)) = 1 := by
  have hr : (2 / 3 : ℚ) = (p : ℚ) / ((p : ℚ) + q) := by
    rw [← hratio]
    norm_num
  have hsum : ((p : ℚ) + q) ≠ 0 := by positivity
  have hpeq : (p : ℚ) = 2 * (q : ℚ) := by
    have hmul : (2 / 3 : ℚ) * ((p : ℚ) + q) = (p : ℚ) := by
      rw [hr]
      exact div_mul_cancel₀ _ hsum
    linarith
  have hp2 : p = 2 * q := by exact_mod_cast hpeq
  have h13 : (((4 : ℚ) - 3) / (0 - 3)) = -(1 / 3) := by norm_num
  rw [h13, hp2]
  have hscale : (belyiPolynomial ℚ (2 * q) q).eval (-(1 / 3)) =
      ((belyiPolynomial ℚ 2 1).eval (-(1 / 3))) ^ q := by
    have h := eval_belyiPolynomial_scale 2 1 q (-(1 / 3))
    rw [Nat.mul_one, Nat.mul_comm q 2] at h
    exact h
  have h21 : (belyiPolynomial ℚ 2 1).eval (-(1 / 3)) = 1 := by
    rw [eval_belyi21]
    norm_num
  rw [hscale, h21, one_pow]

/-- **The plan's STEP 2 is FALSE.**  For S = {0,1,3} with the only normalization pair
(a, b) = (0, 3) the third point is uniquely c = 1; its critical ratio is 1/3 and
B_{p,2p}(4/3) = 1 for every positive p, so no third-point choice avoids the value 1. -/
theorem thirdPointClaim_false : ¬ ThirdPointClaim := by
  intro hclaim
  obtain ⟨c, p, q, hcS, hca, hcb, hp, hq, hratio, hne⟩ :=
    hclaim {0, 1, 3} 4 0 3 (by decide) (by decide) (by decide) (by decide) zero_three_bound
  have hc1 : c = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcS
    rcases hcS with h | h | h
    · exact absurd h hca
    · exact h
    · exact absurd h hcb
  rw [hc1] at hratio
  exact hne (forward_orientation_value_eq_one hp hq hratio)

/-! ## Section E -- value conditions, the step lemma, and the assembly -/

/-- **The exact value conditions needed for the third-point step** (for sets with at least
four points, where the min/max normalization leaves at least two candidates).  This is the
precise remaining gap of the correction. -/
def ThirdPointValueConditions : Prop :=
  ∀ (S : Finset ℚ) (β : ℚ), 4 ≤ S.card → β ∉ S →
    ∃ (a b c : ℚ) (p q : ℕ), a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧
      0 < p ∧ 0 < q ∧ (c - a) / (b - a) = (p : ℚ) / ((p : ℚ) + q) ∧
      (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)) ≠ 1 ∧
      (∀ s ∈ S, s ≠ a → s ≠ b → s ≠ c →
        (belyiPolynomial ℚ p q).eval ((s - a) / (b - a)) ≠
          (belyiPolynomial ℚ p q).eval ((β - a) / (b - a)))

/-- ** exists_card_image_lt_beta ** : the TauCeti exists_card_image_lt shape (a strict
cardinality drop of the image of S, with 0 and 1 in the image and all critical values in
{0,1}) together with the beta-tracking condition f(beta) not in f(S), derived from the
third-point value conditions. -/
theorem exists_card_image_lt_beta (h : ThirdPointValueConditions) :
    ∀ (S : Finset ℚ) (β : ℚ), 4 ≤ S.card → β ∉ S →
      ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
        (S.image (fun x => f.eval x)).card < S.card ∧
        (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
        (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
        f.eval β ∉ S.image (fun x => f.eval x) := by
  intro S β hS hβ
  obtain ⟨a, b, c, p, q, haS, hbS, hcS, hab, hca, hcb, hp, hq, hratio, hV1, hV2⟩ :=
    h S β hS hβ
  exact exists_card_image_lt_beta_of_third_point haS hbS hcS hβ hab hca hcb hp hq hratio
    hV1 hV2

/-- **The assembly.**  A beta-avoiding step lemma for sets with at least four points implies
the full beta-avoiding Belyi construction for every finite set of rational numbers and every
outside rational beta.  The induction is on S.card; the base case |S| <= 3 is the already
proved small statement (belyiBetaAvoidingSmallStatement_proved), the step is applied only for
|S| >= 4 (where the one-layer third-point construction is available), and the composite
q.comp f inherits CritIn01 by critIn01_comp because 0 and 1 lie in f(S). -/
theorem exists_betaAvoiding_of_thirdPoint_step
    (hstep : ∀ (S : Finset ℚ) (β : ℚ), 4 ≤ S.card → β ∉ S →
      ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
        (S.image (fun x => f.eval x)).card < S.card ∧
        (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
        (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
        f.eval β ∉ S.image (fun x => f.eval x)) :
    ∀ (S : Finset ℚ) (β : ℚ), β ∉ S →
      ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
        (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1 := by
  suffices H : ∀ n, ∀ (S : Finset ℚ) (β : ℚ), S.card = n → β ∉ S →
      ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
        (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1 by
    intro S β hβ
    exact H S.card S β rfl hβ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S β hcard hβ
    by_cases hle : S.card ≤ 3
    · have hb :=
        LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingExteriorActual.belyiBetaAvoidingSmallStatement_proved
      unfold BelyiBetaAvoidingSmallStatement at hb
      obtain ⟨q, hqdeg, hqS, hqβ0, hqβ1, hqC⟩ := hb S β hle hβ
      exact ⟨q, hqdeg, hqC, hqS, hqβ0, hqβ1⟩
    · have h4 : 4 ≤ S.card := by omega
      obtain ⟨f, hfdeg, hfC, hTcard, hT0, hT1, hfβ⟩ := hstep S β h4 hβ
      obtain ⟨q, hqdeg, hqC, hqT, hqβ0, hqβ1⟩ :=
        ih (S.image (fun x => f.eval x)).card (by omega) (S.image (fun x => f.eval x))
          (f.eval β) rfl hfβ
      refine ⟨q.comp f, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Polynomial.natDegree_comp]
        exact Nat.mul_pos hqdeg hfdeg
      · exact critIn01_comp hqdeg hfdeg (hqT 0 hT0) (hqT 1 hT1) hqC hfC
      · intro s hs
        rw [Polynomial.eval_comp]
        exact hqT (f.eval s) (Finset.mem_image_of_mem _ hs)
      · intro hh
        rw [Polynomial.eval_comp] at hh
        exact hqβ0 hh
      · intro hh
        rw [Polynomial.eval_comp] at hh
        exact hqβ1 hh

/-- **The beta-avoiding Belyi construction for every finite rational set**, conditional on
the third-point value conditions (and hence on the single remaining third-point lemma). -/
theorem exists_betaAvoiding_of_thirdPoint_valueConditions (h : ThirdPointValueConditions) :
    ∀ (S : Finset ℚ) (β : ℚ), β ∉ S →
      ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
        (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1 :=
  exists_betaAvoiding_of_thirdPoint_step (exists_card_image_lt_beta h)

/-! ## Row record -/

/-- Row record: what is proved and what remains (STEP 1, the step theorem, the interior
case, the refuted STEP 2, and the assembly). -/
def thirdPointRows : List (String × String × String) :=
  [ ("STEP 1: odd scaling B_{kp,kq}(u) = B_{p,q}(u)^k avoids {0,1}", "A",
     "PROVED belyiEvalQ_odd_scale_ne_zero_one / belyiPolynomial_odd_scale_avoids")
  , ("critical ratio invariant under scaling; ratio realization automatic", "A",
     "PROVED div_add_scale / exists_ratio_of_between")
  , ("third-point step with beta tracking (one layer)", "A",
     "PROVED exists_card_image_lt_beta_of_third_point / ..._odd_scale")
  , ("exterior beta: sign version and the odd-parity cases closed", "A",
     "PROVED exists_card_image_lt_beta_of_third_point_sign / ..._of_gt_odd / ..._of_lt_odd")
  , ("interior beta: first value condition automatic (maximizer uniqueness)", "A",
     "PROVED interior_value_ne_one")
  , ("plan STEP 2 (|S| >= 3 candidate with B != 1)", "REFUTED",
     "thirdPointClaim_false; counterexample S = {0,1,3}, beta = 4 (both orientations)")
  , ("third-point value conditions for |S| >= 4", "BLOCKER",
     "NAMED ThirdPointValueConditions; value conditions V1 (extra preimage of 1) and V2 (partner collision)")
  , ("assembly to the full beta-avoiding construction", "A",
     "PROVED exists_card_image_lt_beta / exists_betaAvoiding_of_thirdPoint_step / exists_betaAvoiding_of_thirdPoint_valueConditions") ]

/-- The row record has eight rows. -/
theorem thirdPointRows_length : thirdPointRows.length = 8 := rfl

#check belyiEvalQ_odd_scale_ne_zero_one
#check eval_belyiPolynomial_scale
#check belyiPolynomial_odd_scale_avoids
#check div_add_scale
#check exists_ratio_of_between
#check exists_card_image_lt_beta_of_third_point
#check exists_card_image_lt_beta_of_third_point_odd_scale
#check exists_card_image_lt_beta_of_third_point_sign
#check exists_card_image_lt_beta_of_third_point_of_gt_odd
#check exists_card_image_lt_beta_of_third_point_of_lt_odd
#check interior_value_ne_one
#check ThirdPointClaim
#check thirdPointClaim_false
#check ThirdPointValueConditions
#check exists_card_image_lt_beta
#check exists_betaAvoiding_of_thirdPoint_step
#check exists_betaAvoiding_of_thirdPoint_valueConditions
#check thirdPointRows_length

#print axioms belyiEvalQ_odd_scale_ne_zero_one
#print axioms belyiPolynomial_odd_scale_avoids
#print axioms div_add_scale
#print axioms exists_ratio_of_between
#print axioms exists_card_image_lt_beta_of_third_point
#print axioms exists_card_image_lt_beta_of_third_point_odd_scale
#print axioms exists_card_image_lt_beta_of_third_point_sign
#print axioms exists_card_image_lt_beta_of_third_point_of_gt_odd
#print axioms exists_card_image_lt_beta_of_third_point_of_lt_odd
#print axioms interior_value_ne_one
#print axioms forward_orientation_value_eq_one
#print axioms backward_orientation_value_eq_one
#print axioms thirdPointClaim_false
#print axioms exists_card_image_lt_beta
#print axioms exists_betaAvoiding_of_thirdPoint_step
#print axioms exists_betaAvoiding_of_thirdPoint_valueConditions
#print axioms thirdPointRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingThirdPointActual