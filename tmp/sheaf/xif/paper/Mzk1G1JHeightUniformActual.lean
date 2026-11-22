import tmp.sheaf.xif.paper.Mzk1G1JHeightUniformProbeActual
import tmp.sheaf.xif.paper.Mzk1G1JHeightBezoutActual
import tmp.sheaf.xif.paper.Mzk1G1JHeightD3Actual
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1JHeightUniformActual
open LeanFormal.IUT
open MvPolynomial
open LeanFormal.IUT.XiFPaper.G1QHeightActual
open LeanFormal.IUT.XiFPaper.G1JHeightBezoutActual
open LeanFormal.IUT.XiFPaper.G1JHeightD3Actual
open LeanFormal.IUT.XiFPaper.G1JHeightUniformProbeActual

/-! ## Step 1: the integer coefficient size functional S -/

/-- Sum of the absolute values of the integer coefficients of a polynomial. -/
def coeffAbsSum (p : MvPolynomial (Fin 2) ℤ) : ℕ :=
  p.support.sum fun s => (MvPolynomial.coeff s p).natAbs

lemma coeffAbsSum_coeff_le (p : MvPolynomial (Fin 2) ℤ) (s : Fin 2 →₀ ℕ) :
    (MvPolynomial.coeff s p).natAbs ≤ coeffAbsSum p := by
  unfold coeffAbsSum
  by_cases hs : s ∈ p.support
  · exact Finset.single_le_sum (f := fun s => (MvPolynomial.coeff s p).natAbs)
      (fun i _ => Nat.zero_le _) hs
  · have hzero : MvPolynomial.coeff s p = 0 := MvPolynomial.notMem_support_iff.mp hs
    simp [hzero]

lemma coeffAbsSum_add_le (p q : MvPolynomial (Fin 2) ℤ) :
    coeffAbsSum (p + q) ≤ coeffAbsSum p + coeffAbsSum q := by
  unfold coeffAbsSum
  have hpq : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  have hzero_p : ∀ s ∈ p.support ∪ q.support, s ∉ p.support →
      (MvPolynomial.coeff s p).natAbs = 0 := fun s _ hs => by
    rw [MvPolynomial.notMem_support_iff.mp hs]; simp
  have hzero_q : ∀ s ∈ p.support ∪ q.support, s ∉ q.support →
      (MvPolynomial.coeff s q).natAbs = 0 := fun s _ hs => by
    rw [MvPolynomial.notMem_support_iff.mp hs]; simp
  have hint : (p + q).support.sum (fun s => (MvPolynomial.coeff s (p + q)).natAbs)
      ≤ p.support.sum (fun s => (MvPolynomial.coeff s p).natAbs)
        + q.support.sum (fun s => (MvPolynomial.coeff s q).natAbs) := by
    calc (p + q).support.sum (fun s => (MvPolynomial.coeff s (p + q)).natAbs)
        ≤ (p + q).support.sum (fun s =>
            (MvPolynomial.coeff s p).natAbs + (MvPolynomial.coeff s q).natAbs) := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [MvPolynomial.coeff_add]
          exact Int.natAbs_add_le _ _
      _ = ((p + q).support.sum (fun s => (MvPolynomial.coeff s p).natAbs))
            + ((p + q).support.sum (fun s => (MvPolynomial.coeff s q).natAbs)) :=
          Finset.sum_add_distrib
      _ ≤ p.support.sum (fun s => (MvPolynomial.coeff s p).natAbs)
            + q.support.sum (fun s => (MvPolynomial.coeff s q).natAbs) := by
          refine add_le_add ?_ ?_
          · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hpq ?_)
              (le_of_eq ?_)
            · intro x _ _; exact Nat.zero_le _
            · exact (Finset.sum_subset (Finset.subset_union_left) hzero_p).symm
          · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hpq ?_)
              (le_of_eq ?_)
            · intro x _ _; exact Nat.zero_le _
            · exact (Finset.sum_subset (Finset.subset_union_right) hzero_q).symm
  exact hint

lemma coeffAbsSum_C_mul_le (a : ℤ) (p : MvPolynomial (Fin 2) ℤ) :
    coeffAbsSum (MvPolynomial.C a * p) ≤ a.natAbs * coeffAbsSum p := by
  unfold coeffAbsSum
  have hsupp : (MvPolynomial.C a * p).support ⊆ p.support := by
    rw [MvPolynomial.C_mul']
    exact MvPolynomial.support_smul
  calc (MvPolynomial.C a * p).support.sum
        (fun s => (MvPolynomial.coeff s (MvPolynomial.C a * p)).natAbs)
      ≤ (MvPolynomial.C a * p).support.sum
          (fun s => a.natAbs * (MvPolynomial.coeff s p).natAbs) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [MvPolynomial.coeff_C_mul, Int.natAbs_mul]
    _ = a.natAbs * ((MvPolynomial.C a * p).support.sum
          (fun s => (MvPolynomial.coeff s p).natAbs)) := by
        rw [Finset.mul_sum]
    _ ≤ a.natAbs * (p.support.sum (fun s => (MvPolynomial.coeff s p).natAbs)) := by
        refine Nat.mul_le_mul_left _ ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg hsupp ?_
        intro x _ _; exact Nat.zero_le _

#print axioms coeffAbsSum_coeff_le
#print axioms coeffAbsSum_add_le
#print axioms coeffAbsSum_C_mul_le

/-- Integer coefficients of a polynomial of total degree D are supported on at
most (D+1)^2 monomials. -/
lemma support_card_le (p : MvPolynomial (Fin 2) ℤ) (D : ℕ) (hD : p.totalDegree ≤ D) :
    p.support.card ≤ (D + 1) ^ 2 := by
  classical
  have hbound : ∀ s ∈ p.support, ∀ i : Fin 2, s i ≤ D := by
    intro s hs i
    have hdeg : s.sum (fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
    have hsle : s i ≤ s.sum (fun _ e => e) := by
      by_cases hi : s i = 0
      · rw [hi]; exact Nat.zero_le _
      · simpa [Finsupp.sum] using
          Finset.single_le_sum (f := fun j => s j) (fun j _ => Nat.zero_le _)
            (Finsupp.mem_support_iff.mpr hi)
    exact le_trans hsle (le_trans hdeg hD)
  let f : (Fin 2 →₀ ℕ) → (Fin 2 → Fin (D + 1)) := fun s =>
    if hs : s ∈ p.support then fun i => ⟨s i, Nat.lt_succ_of_le (hbound s hs i)⟩
    else fun _ => 0
  have hmaps : Set.MapsTo f (↑p.support) (↑(Finset.univ : Finset (Fin 2 → Fin (D + 1)))) :=
    fun s _ => Finset.mem_univ _
  have hinj : (↑p.support : Set (Fin 2 →₀ ℕ)).InjOn f := by
    intro s hs t ht hst
    have hs' : s ∈ p.support := hs
    have ht' : t ∈ p.support := ht
    have hsdef : f s = fun i => (⟨s i, Nat.lt_succ_of_le (hbound s hs' i)⟩ : Fin (D + 1)) := by
      simp only [f, dif_pos hs']
    have htdef : f t = fun i => (⟨t i, Nat.lt_succ_of_le (hbound t ht' i)⟩ : Fin (D + 1)) := by
      simp only [f, dif_pos ht']
    ext i
    have h := congrFun hst i
    rw [hsdef, htdef] at h
    exact Fin.ext_iff.mp h
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  calc p.support.card ≤ (Finset.univ : Finset (Fin 2 → Fin (D + 1))).card := hcard
    _ = (D + 1) ^ 2 := by simp [Fintype.card_fun]

/-- The convolution bound for the coefficient size functional. -/
lemma coeffAbsSum_mul_le (p q : MvPolynomial (Fin 2) ℤ) :
    coeffAbsSum (p * q) ≤
      (p * q).support.card * (q.support.card * (coeffAbsSum p * coeffAbsSum q)) := by
  have hcoeff : ∀ s : Fin 2 →₀ ℕ,
      (MvPolynomial.coeff s (p * q)).natAbs
        ≤ q.support.card * (coeffAbsSum p * coeffAbsSum q) := by
    intro s
    rw [MvPolynomial.coeff_mul]
    set T : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) :=
      (Finset.antidiagonal s).filter (fun x => x.2 ∈ q.support) with hT
    have h1 : (∑ x ∈ Finset.antidiagonal s,
        (MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q)).natAbs
        ≤ ∑ x ∈ Finset.antidiagonal s,
            (MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q).natAbs :=
      Int.natAbs_sum_le _ _
    have h2 : (∑ x ∈ Finset.antidiagonal s,
        (MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q).natAbs)
        = ∑ x ∈ T, (MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q).natAbs := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro x hxS hxT
      have hxq : x.2 ∉ q.support := by
        intro hmem
        exact hxT (Finset.mem_filter.mpr ⟨hxS, hmem⟩)
      have hzero : MvPolynomial.coeff x.2 q = 0 := MvPolynomial.notMem_support_iff.mp hxq
      simp [hzero]
    have hterm2 : ∀ x ∈ T,
        (MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q).natAbs
          ≤ coeffAbsSum p * coeffAbsSum q := by
      intro x _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (coeffAbsSum_coeff_le p x.1) (coeffAbsSum_coeff_le q x.2)
    have h3 : (∑ x ∈ T, (MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q).natAbs)
        ≤ T.card * (coeffAbsSum p * coeffAbsSum q) := by
      calc (∑ x ∈ T, (MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q).natAbs)
          ≤ ∑ _x ∈ T, (coeffAbsSum p * coeffAbsSum q) := Finset.sum_le_sum hterm2
        _ = T.card * (coeffAbsSum p * coeffAbsSum q) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    have h4 : T.card ≤ q.support.card := by
      refine Finset.card_le_card_of_injOn (fun x : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => x.2) ?_ ?_
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro x hx y hy hxy
        have hxanti : x.1 + x.2 = s := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hx).1
        have hyanti : y.1 + y.2 = s := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hy).1
        have h1 : x.1 = y.1 := by
          ext i
          have hxi := congrArg (fun z : Fin 2 →₀ ℕ => z i) hxanti
          have hyi := congrArg (fun z : Fin 2 →₀ ℕ => z i) hyanti
          have hxy' := congrArg (fun z : Fin 2 →₀ ℕ => z i) hxy
          simp only [Finsupp.add_apply] at hxi hyi hxy'
          omega
        exact Prod.ext h1 hxy
    exact le_trans h1 (le_trans (le_trans (le_of_eq h2) h3) (Nat.mul_le_mul_right _ h4))
  calc coeffAbsSum (p * q)
      = ∑ s ∈ (p * q).support, (MvPolynomial.coeff s (p * q)).natAbs := rfl
    _ ≤ ∑ _s ∈ (p * q).support, (q.support.card * (coeffAbsSum p * coeffAbsSum q)) :=
        Finset.sum_le_sum fun s _ => hcoeff s
    _ = (p * q).support.card * (q.support.card * (coeffAbsSum p * coeffAbsSum q)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

#print axioms support_card_le
#print axioms coeffAbsSum_mul_le



lemma coeffAbsSum_neg (p : MvPolynomial (Fin 2) ℤ) : coeffAbsSum (-p) = coeffAbsSum p := by
  unfold coeffAbsSum
  rw [MvPolynomial.support_neg]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_neg, Int.natAbs_neg]

lemma coeffAbsSum_sub_le (p q : MvPolynomial (Fin 2) ℤ) :
    coeffAbsSum (p - q) ≤ coeffAbsSum p + coeffAbsSum q := by
  rw [sub_eq_add_neg]
  have h := coeffAbsSum_add_le p (-q)
  rwa [coeffAbsSum_neg] at h
/-- The quadratic factor `1 - lam + lam^2` as a two-variable integer polynomial. -/
def polyZ : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2

lemma coeffAbsSum_X_pow (i : Fin 2) (n : ℕ) :
    coeffAbsSum (MvPolynomial.X i ^ n : MvPolynomial (Fin 2) ℤ) = 1 := by
  rw [MvPolynomial.X_pow_eq_monomial]
  simp [coeffAbsSum, MvPolynomial.support_monomial]

lemma coeffAbsSum_X_pow_mul_X_pow (a b : ℕ) :
    coeffAbsSum (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) ℤ) = 1 := by
  have h : (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) ℤ)
      = MvPolynomial.monomial (Finsupp.single 0 a + Finsupp.single 1 b) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, one_mul]
  rw [h]
  simp [coeffAbsSum, MvPolynomial.support_monomial]

lemma coeffAbsSum_polyZ_le : coeffAbsSum polyZ ≤ 3 := by
  have h1 := coeffAbsSum_add_le (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1)
    (MvPolynomial.X 1 ^ 2)
  have h2 := coeffAbsSum_sub_le (MvPolynomial.X 0 ^ 2) (MvPolynomial.X 0 * MvPolynomial.X 1)
  have h3 : coeffAbsSum (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) = 1 :=
    coeffAbsSum_X_pow 0 2
  have h4 : coeffAbsSum (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) = 1 := by
    simpa using coeffAbsSum_X_pow_mul_X_pow 1 1
  have h5 : coeffAbsSum (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) = 1 :=
    coeffAbsSum_X_pow 1 2
  unfold polyZ
  omega

lemma numeral_eq_C_int (n : ℕ) :
    (n : MvPolynomial (Fin 2) ℤ) = MvPolynomial.C ((n : ℕ) : ℤ) := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (map_natCast (algebraMap ℤ (MvPolynomial (Fin 2) ℤ)) n).symm

#print axioms coeffAbsSum_X_pow
#print axioms coeffAbsSum_X_pow_mul_X_pow
#print axioms coeffAbsSum_polyZ_le
#print axioms numeral_eq_C_int


/-! ## Step 3b: explicit bounds for S of the concrete polynomials -/

/-- S of the quadratic factor. -/
def Sp : ℕ := coeffAbsSum polyZ
/-- Total degree of the quadratic factor (kept symbolic to avoid unfolding). -/
def Dp : ℕ := polyZ.totalDegree
def Np : ℕ := (Dp + 1) ^ 2
def Np2 : ℕ := (2 * Dp + 1) ^ 2
def Np3 : ℕ := (3 * Dp + 1) ^ 2
def Sp2 : ℕ := Np2 * (Np * (3 * 3))
def Sp3 : ℕ := Np3 * (Np * (Sp2 * 3))
def S_jNum : ℕ := 256 * Sp3
def qShift : MvPolynomial (Fin 2) ℤ := (MvPolynomial.X 1 - MvPolynomial.X 0) ^ 2
def NqShift : ℕ := (qShift.totalDegree + 1) ^ 2
def NjDen : ℕ := (jDenZ.totalDegree + 1) ^ 2
def S_jDen : ℕ := NjDen * (NqShift * (1 * 4))

lemma nat_mul_coeffAbsSum_le (n : ℕ) (p : MvPolynomial (Fin 2) ℤ) :
    coeffAbsSum ((n : MvPolynomial (Fin 2) ℤ) * p) ≤ n * coeffAbsSum p := by
  rw [numeral_eq_C_int n]
  simpa using coeffAbsSum_C_mul_le (n : ℤ) p

lemma neg_nat_mul_coeffAbsSum_le (n : ℕ) (p : MvPolynomial (Fin 2) ℤ) :
    coeffAbsSum ((-(n : MvPolynomial (Fin 2) ℤ)) * p) ≤ n * coeffAbsSum p := by
  rw [neg_mul, coeffAbsSum_neg]
  exact nat_mul_coeffAbsSum_le n p

lemma support_card_polyZ_le : polyZ.support.card ≤ Np := by
  unfold Np Dp
  exact support_card_le polyZ polyZ.totalDegree le_rfl

lemma support_card_polyZ2_le : (polyZ ^ 2).support.card ≤ Np2 := by
  have hD : (polyZ ^ 2).totalDegree ≤ 2 * Dp := by
    simpa [Dp] using MvPolynomial.totalDegree_pow (polyZ : MvPolynomial (Fin 2) ℤ) 2
  calc (polyZ ^ 2).support.card ≤ ((polyZ ^ 2).totalDegree + 1) ^ 2 :=
        support_card_le _ _ le_rfl
    _ ≤ Np2 := by
        unfold Np2
        exact Nat.pow_le_pow_left (by omega) 2

lemma support_card_polyZ3_le : (polyZ ^ 3).support.card ≤ Np3 := by
  have hD : (polyZ ^ 3).totalDegree ≤ 3 * Dp := by
    simpa [Dp] using MvPolynomial.totalDegree_pow (polyZ : MvPolynomial (Fin 2) ℤ) 3
  calc (polyZ ^ 3).support.card ≤ ((polyZ ^ 3).totalDegree + 1) ^ 2 :=
        support_card_le _ _ le_rfl
    _ ≤ Np3 := by
        unfold Np3
        exact Nat.pow_le_pow_left (by omega) 2

lemma coeffAbsSum_polyZ2_le : coeffAbsSum (polyZ ^ 2) ≤ Sp2 := by
  have h := coeffAbsSum_mul_le polyZ polyZ
  have h2 : (polyZ ^ 2).support.card ≤ Np2 := support_card_polyZ2_le
  rw [pow_two] at h2 ⊢
  refine h.trans ?_
  unfold Sp2
  exact Nat.mul_le_mul h2 (Nat.mul_le_mul support_card_polyZ_le
    (Nat.mul_le_mul coeffAbsSum_polyZ_le coeffAbsSum_polyZ_le))

lemma coeffAbsSum_polyZ3_le : coeffAbsSum (polyZ ^ 3) ≤ Sp3 := by
  have h := coeffAbsSum_mul_le (polyZ ^ 2) polyZ
  have h2 : (polyZ ^ 3).support.card ≤ Np3 := support_card_polyZ3_le
  rw [pow_succ] at h2 ⊢
  refine h.trans ?_
  unfold Sp3
  exact Nat.mul_le_mul h2 (Nat.mul_le_mul support_card_polyZ_le
    (Nat.mul_le_mul coeffAbsSum_polyZ2_le coeffAbsSum_polyZ_le))

lemma jNumZ_eq_C : jNumZ = MvPolynomial.C (256 : ℤ) * polyZ ^ 3 := by
  have h256 : (256 : MvPolynomial (Fin 2) ℤ) = MvPolynomial.C (256 : ℤ) := by
    simpa using numeral_eq_C_int 256
  unfold jNumZ polyZ
  rw [h256]

lemma coeffAbsSum_jNumZ_le : coeffAbsSum jNumZ ≤ S_jNum := by
  rw [jNumZ_eq_C]
  calc coeffAbsSum (MvPolynomial.C (256 : ℤ) * polyZ ^ 3)
      ≤ (256 : ℤ).natAbs * coeffAbsSum (polyZ ^ 3) := coeffAbsSum_C_mul_le 256 _
    _ ≤ 256 * Sp3 := by
        have h : (256 : ℤ).natAbs = 256 := by norm_num
        rw [h]
        exact Nat.mul_le_mul_left _ coeffAbsSum_polyZ3_le
    _ = S_jNum := rfl

lemma coeffAbsSum_qShift_le : coeffAbsSum qShift ≤ 4 := by
  have heq : qShift = (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℤ)
      - (2 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 * MvPolynomial.X 1)
      + MvPolynomial.X 0 ^ 2 := by
    unfold qShift; ring
  rw [heq]
  have h1 := coeffAbsSum_add_le
    ((MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℤ)
      - (2 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 * MvPolynomial.X 1))
    (MvPolynomial.X 0 ^ 2)
  have h2 := coeffAbsSum_sub_le (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℤ)
    ((2 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 * MvPolynomial.X 1))
  have h3 : coeffAbsSum ((2 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 * MvPolynomial.X 1)) ≤ 2 := by
    have h := nat_mul_coeffAbsSum_le 2 (MvPolynomial.X 0 * MvPolynomial.X 1)
    have hS : coeffAbsSum (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) = 1 := by
      simpa using coeffAbsSum_X_pow_mul_X_pow 1 1
    rw [hS] at h
    simpa using h
  have h4 : coeffAbsSum (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) = 1 :=
    coeffAbsSum_X_pow 1 2
  have h5 : coeffAbsSum (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) = 1 :=
    coeffAbsSum_X_pow 0 2
  calc coeffAbsSum (MvPolynomial.X 1 ^ 2 - (2 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 * MvPolynomial.X 1) + MvPolynomial.X 0 ^ 2)
      ≤ coeffAbsSum (MvPolynomial.X 1 ^ 2 - (2 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 * MvPolynomial.X 1))
          + coeffAbsSum (MvPolynomial.X 0 ^ 2) := h1
    _ ≤ (coeffAbsSum (MvPolynomial.X 1 ^ 2) + coeffAbsSum ((2 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 * MvPolynomial.X 1)))
          + coeffAbsSum (MvPolynomial.X 0 ^ 2) := by
        gcongr
    _ ≤ (1 + 2) + 1 := add_le_add (add_le_add (le_of_eq h4) h3) (le_of_eq h5)
    _ = 4 := by norm_num

lemma support_card_qShift_le : qShift.support.card ≤ NqShift := by
  unfold NqShift
  exact support_card_le qShift qShift.totalDegree le_rfl

lemma support_card_jDenZ_le : jDenZ.support.card ≤ NjDen := by
  unfold NjDen
  exact support_card_le jDenZ jDenZ.totalDegree le_rfl

lemma coeffAbsSum_jDenZ_le : coeffAbsSum jDenZ ≤ S_jDen := by
  have h := coeffAbsSum_mul_le
    (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) qShift
  have hden : jDenZ = (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2) * qShift := rfl
  rw [hden]
  refine h.trans ?_
  unfold S_jDen
  exact Nat.mul_le_mul support_card_jDenZ_le (Nat.mul_le_mul support_card_qShift_le
    (Nat.mul_le_mul (le_of_eq (coeffAbsSum_X_pow_mul_X_pow 2 2)) coeffAbsSum_qShift_le))

#print axioms coeffAbsSum_polyZ2_le
#print axioms coeffAbsSum_polyZ3_le
#print axioms coeffAbsSum_jNumZ_le
#print axioms coeffAbsSum_jDenZ_le


/-! ## Step 3c: S bounds for the four Bezout coefficient polynomials -/

def S_Q : ℕ := 8704

lemma S_nat_mon_mul_le (n a b : ℕ) :
    coeffAbsSum ((n : MvPolynomial (Fin 2) ℤ)
      * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) ≤ n := by
  have h := nat_mul_coeffAbsSum_le n (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)
  rw [coeffAbsSum_X_pow_mul_X_pow a b] at h
  simpa using h

lemma S_neg_nat_mon_mul_le (n a b : ℕ) :
    coeffAbsSum ((-(n : MvPolynomial (Fin 2) ℤ))
      * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) ≤ n := by
  have h := neg_nat_mul_coeffAbsSum_le n (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)
  rw [coeffAbsSum_X_pow_mul_X_pow a b] at h
  simpa using h

lemma coeffAbsSum_jQ00Z_le : coeffAbsSum jQ00Z ≤ S_Q := by
  unfold jQ00Z
  have h1 := coeffAbsSum_add_le
    ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
      + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1))
    ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))
  have h2 := coeffAbsSum_add_le
    ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))
    ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1))
  calc coeffAbsSum ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
        + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1)
        + (1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))
      ≤ coeffAbsSum ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
          + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1))
        + coeffAbsSum ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)) := h1
    _ ≤ (coeffAbsSum ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))
          + coeffAbsSum ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1)))
        + coeffAbsSum ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)) := by
        gcongr
    _ ≤ ((3 + 3) + 1) := by
        exact add_le_add (add_le_add (by simpa using S_neg_nat_mon_mul_le 3 2 2) (by simpa using S_nat_mon_mul_le 3 3 1))
          (by simpa using S_nat_mon_mul_le 1 4 0)
    _ ≤ S_Q := by unfold S_Q; norm_num

lemma coeffAbsSum_jQ10Z_le : coeffAbsSum jQ10Z ≤ S_Q := by
  unfold jQ10Z
  have h1 := coeffAbsSum_add_le
    ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
      + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3))
    ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))
  have h2 := coeffAbsSum_add_le
    ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4))
    ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3))
  calc coeffAbsSum ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
        + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
        + (-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))
      ≤ coeffAbsSum ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
          + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3))
        + coeffAbsSum ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)) := h1
    _ ≤ (coeffAbsSum ((1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4))
          + coeffAbsSum ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)))
        + coeffAbsSum ((-(3 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)) := by
        gcongr
    _ ≤ ((1 + 3) + 3) := by
        exact add_le_add (add_le_add (by simpa using S_nat_mon_mul_le 1 0 4) (by simpa using S_nat_mon_mul_le 3 1 3))
          (by simpa using S_neg_nat_mon_mul_le 3 2 2)
    _ ≤ S_Q := by unfold S_Q; norm_num


#print axioms coeffAbsSum_jQ00Z_le
#print axioms coeffAbsSum_jQ10Z_le

lemma coeffAbsSum_add4_le (a b c d : MvPolynomial (Fin 2) ℤ) (A B C D : ℕ)
    (ha : coeffAbsSum a ≤ A) (hb : coeffAbsSum b ≤ B) (hc : coeffAbsSum c ≤ C)
    (hd : coeffAbsSum d ≤ D) :
    coeffAbsSum (((a + b) + c) + d) ≤ ((A + B) + C) + D := by
  have h1 := coeffAbsSum_add_le ((a + b) + c) d
  have h2 := coeffAbsSum_add_le (a + b) c
  have h3 := coeffAbsSum_add_le a b
  calc coeffAbsSum (((a + b) + c) + d) ≤ coeffAbsSum ((a + b) + c) + coeffAbsSum d := h1
    _ ≤ (coeffAbsSum (a + b) + coeffAbsSum c) + coeffAbsSum d := by gcongr
    _ ≤ ((coeffAbsSum a + coeffAbsSum b) + coeffAbsSum c) + coeffAbsSum d := by gcongr
    _ ≤ ((A + B) + C) + D := by
        exact add_le_add (add_le_add (add_le_add ha hb) hc) hd

lemma coeffAbsSum_add5_le (a b c d e : MvPolynomial (Fin 2) ℤ) (A B C D E : ℕ)
    (ha : coeffAbsSum a ≤ A) (hb : coeffAbsSum b ≤ B) (hc : coeffAbsSum c ≤ C)
    (hd : coeffAbsSum d ≤ D) (he : coeffAbsSum e ≤ E) :
    coeffAbsSum ((((a + b) + c) + d) + e) ≤ (((A + B) + C) + D) + E := by
  have h1 := coeffAbsSum_add_le (((a + b) + c) + d) e
  have h4 := coeffAbsSum_add4_le a b c d A B C D ha hb hc hd
  calc coeffAbsSum ((((a + b) + c) + d) + e)
      ≤ coeffAbsSum (((a + b) + c) + d) + coeffAbsSum e := h1
    _ ≤ (((A + B) + C) + D) + E := by
        exact add_le_add h4 he

lemma coeffAbsSum_jQ01Z_le : coeffAbsSum jQ01Z ≤ S_Q := by
  unfold jQ01Z
  set inner : MvPolynomial (Fin 2) ℤ :=
    (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
      + (-(6 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
      + (11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
      + (-(8 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
      + (6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0) with hInner
  change coeffAbsSum ((256 : MvPolynomial (Fin 2) ℤ) * inner) ≤ S_Q
  have hinner : coeffAbsSum inner ≤ 34 := by
    rw [hInner]
    have h := coeffAbsSum_add5_le
      ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4))
      ((-(6 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3))
      ((11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))
      ((-(8 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1))
      ((6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))
      3 6 11 8 6
      (by simpa using S_nat_mon_mul_le 3 0 4)
      (by simpa using S_neg_nat_mon_mul_le 6 1 3)
      (by simpa using S_nat_mon_mul_le 11 2 2)
      (by simpa using S_neg_nat_mon_mul_le 8 3 1)
      (by simpa using S_nat_mon_mul_le 6 4 0)
    exact h.trans (by norm_num)
  have hout := nat_mul_coeffAbsSum_le 256 inner
  exact (hout.trans (Nat.mul_le_mul_left 256 hinner)).trans (by unfold S_Q; norm_num)


lemma coeffAbsSum_jQ11Z_le : coeffAbsSum jQ11Z ≤ S_Q := by
  unfold jQ11Z
  set inner : MvPolynomial (Fin 2) ℤ :=
    (6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
      + (-(8 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
      + (11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
      + (-(6 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
      + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0) with hInner
  change coeffAbsSum ((256 : MvPolynomial (Fin 2) ℤ) * inner) ≤ S_Q
  have hinner : coeffAbsSum inner ≤ 34 := by
    rw [hInner]
    have h := coeffAbsSum_add5_le
      ((6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4))
      ((-(8 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3))
      ((11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))
      ((-(6 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1))
      ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))
      6 8 11 6 3
      (by simpa using S_nat_mon_mul_le 6 0 4)
      (by simpa using S_neg_nat_mon_mul_le 8 1 3)
      (by simpa using S_nat_mon_mul_le 11 2 2)
      (by simpa using S_neg_nat_mon_mul_le 6 3 1)
      (by simpa using S_nat_mon_mul_le 3 4 0)
    exact h.trans (by norm_num)
  have hout := nat_mul_coeffAbsSum_le 256 inner
  exact (hout.trans (Nat.mul_le_mul_left 256 hinner)).trans (by unfold S_Q; norm_num)

#print axioms coeffAbsSum_jQ01Z_le
#print axioms coeffAbsSum_jQ11Z_le

variable {K : Type*} [Field K] [NumberField K]

/-! ## Step 3d: transport of the integer models to K -/

theorem jNumZ_map : (jNumZ).map (Int.castRingHom K) = jNumN (K := K) := by
  unfold jNumZ jNumN
  simp only [map_one, map_mul, map_pow, map_add, map_sub, map_neg, map_ofNat,
    MvPolynomial.map_X, map_natCast]

theorem jDenZ_map : (jDenZ).map (Int.castRingHom K) = jDenN (K := K) := by
  unfold jDenZ jDenN
  simp only [map_one, map_mul, map_pow, map_sub, map_neg, map_ofNat, MvPolynomial.map_X]

theorem jQ00Z_map : (jQ00Z).map (Int.castRingHom K) = Q00N (K := K) := by
  unfold jQ00Z Q00N
  simp only [map_one, map_add, map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.map_X]

theorem jQ01Z_map : (jQ01Z).map (Int.castRingHom K) = Q01N (K := K) := by
  unfold jQ01Z Q01N
  simp only [map_one, map_add, map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.map_X]

theorem jQ10Z_map : (jQ10Z).map (Int.castRingHom K) = Q10N (K := K) := by
  unfold jQ10Z Q10N
  simp only [map_one, map_add, map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.map_X]

theorem jQ11Z_map : (jQ11Z).map (Int.castRingHom K) = Q11N (K := K) := by
  unfold jQ11Z Q11N
  simp only [map_one, map_add, map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.map_X]

#print axioms jNumZ_map
#print axioms jDenZ_map
#print axioms jQ00Z_map
#print axioms jQ01Z_map
#print axioms jQ10Z_map
#print axioms jQ11Z_map

/-! ## Step 4: archimedean/nonarchimedean bounds for mulHeightBound -/

lemma mulHeightBound_map_le {ι' : Type*} [Fintype ι'] [Nonempty ι']
    (p : ι' → MvPolynomial (Fin 2) ℤ) (N S : ℕ)
    (hN : ∀ j, (p j).support.card ≤ N)
    (hS : ∀ j s, (MvPolynomial.coeff s (p j)).natAbs ≤ S) :
    Height.mulHeightBound (fun j => (p j).map (Int.castRingHom K))
      ≤ ((N * S : ℕ) : ℝ) ^ Module.finrank ℚ K := by
  set C : ℝ := ((N * S : ℕ) : ℝ) with hC
  rw [Height.mulHeightBound_eq, NumberField.prod_archAbsVal_eq]
  have hsupp : ∀ j, ((p j).map (Int.castRingHom K)).support.card ≤ N := by
    intro j
    rw [MvPolynomial.support_map_of_injective _ Int.cast_injective]
    exact hN j
  have harch : ∀ v : NumberField.InfinitePlace K,
      (⨆ j, (AddMonoidAlgebra.coeff ((p j).map (Int.castRingHom K))).sum (fun _ c => v c)) ≤ C := by
    intro v
    apply ciSup_le
    intro j
    rw [MvPolynomial.sum_def]
    have hterm : ∀ s ∈ ((p j).map (Int.castRingHom K)).support,
        v (MvPolynomial.coeff s ((p j).map (Int.castRingHom K))) ≤ (S : ℝ) := by
      intro s hs
      rw [MvPolynomial.coeff_map]
      change v (((MvPolynomial.coeff s (p j) : ℤ)) : K) ≤ (S : ℝ)
      rw [infPlace_intCast]
      have hc := hS j s
      have habs : |(((MvPolynomial.coeff s (p j) : ℤ)) : ℝ)| =
          ((MvPolynomial.coeff s (p j)).natAbs : ℝ) := by
        have h : ((((MvPolynomial.coeff s (p j)).natAbs : ℤ)) : ℝ) =
            |(((MvPolynomial.coeff s (p j) : ℤ)) : ℝ)| := by
          rw [Int.natCast_natAbs]
          exact Int.cast_abs
        exact h.symm
      rw [habs]
      exact_mod_cast hc
    calc ∑ s ∈ ((p j).map (Int.castRingHom K)).support,
          v (MvPolynomial.coeff s ((p j).map (Int.castRingHom K)))
        ≤ ∑ _s ∈ ((p j).map (Int.castRingHom K)).support, (S : ℝ) := Finset.sum_le_sum hterm
      _ = (((p j).map (Int.castRingHom K)).support.card : ℝ) * S := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * S := by
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg S)
          exact_mod_cast hsupp j
      _ = C := by simp [C, Nat.cast_mul]
  have harch_nonneg : ∀ v : NumberField.InfinitePlace K,
      0 ≤ (⨆ j, (AddMonoidAlgebra.coeff ((p j).map (Int.castRingHom K))).sum (fun _ c => v c)) := by
    intro v
    exact Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun s _ => AbsoluteValue.nonneg (v.1) _))
  have harchprod : (∏ v : NumberField.InfinitePlace K,
      (⨆ j, (AddMonoidAlgebra.coeff ((p j).map (Int.castRingHom K))).sum (fun _ c => v c)) ^ v.mult)
      ≤ ∏ v : NumberField.InfinitePlace K, C ^ v.mult := by
    refine Finset.prod_le_prod (fun v _ => pow_nonneg (harch_nonneg v) _) (fun v _ => ?_)
    exact pow_le_pow_left₀ (harch_nonneg v) (harch v) _

  have hnon : (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
      (⨆ j, max (⨆ s : ↥((p j).map (Int.castRingHom K)).support,
        v.val (MvPolynomial.coeff (↑s) ((p j).map (Int.castRingHom K)))) 1)) = 1 := by
    refine finprod_eq_one_of_forall_eq_one ?_
    intro v
    have hle : ∀ j, (⨆ s : ↥((p j).map (Int.castRingHom K)).support,
        v.val (MvPolynomial.coeff (↑s) ((p j).map (Int.castRingHom K)))) ≤ 1 := by
      intro j
      refine Real.iSup_le (fun s => ?_) zero_le_one
      rw [MvPolynomial.coeff_map]
      obtain ⟨w, hw⟩ := (NumberField.isFinitePlace_iff v.val).mp v.property
      rw [← hw]
      exact finPlace_intCast_le_one w (MvPolynomial.coeff (↑s) (p j))
    have hmax : ∀ j, max (⨆ s : ↥((p j).map (Int.castRingHom K)).support,
        v.val (MvPolynomial.coeff (↑s) ((p j).map (Int.castRingHom K)))) 1 = 1 :=
      fun j => max_eq_right (hle j)
    rw [show (fun j => max (⨆ s : ↥((p j).map (Int.castRingHom K)).support,
        v.val (MvPolynomial.coeff (↑s) ((p j).map (Int.castRingHom K)))) 1)
        = fun _ => (1 : ℝ) from funext hmax]
    simp
  have hprodC : (∏ v : NumberField.InfinitePlace K, C ^ v.mult) = C ^ (Height.totalWeight K) := by
    rw [Finset.prod_pow_eq_pow_sum, NumberField.totalWeight_eq_sum_mult]
  calc (∏ v : NumberField.InfinitePlace K,
        (⨆ j, (AddMonoidAlgebra.coeff ((p j).map (Int.castRingHom K))).sum (fun _ c => v c)) ^ v.mult)
        * (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
          (⨆ j, max (⨆ s : ↥((p j).map (Int.castRingHom K)).support,
            v.val (MvPolynomial.coeff (↑s) ((p j).map (Int.castRingHom K)))) 1))
      ≤ (∏ v : NumberField.InfinitePlace K, C ^ v.mult) * 1 := by
          refine mul_le_mul harchprod (le_of_eq hnon) (finprod_nonneg fun v => ?_) (Finset.prod_nonneg fun v _ => pow_nonneg (by positivity) _)
          exact Real.iSup_nonneg (fun j => le_trans zero_le_one (le_max_right _ _))
    _ = C ^ (Module.finrank ℚ K) := by
        rw [mul_one, hprodC, NumberField.totalWeight_eq_finrank]

#print axioms mulHeightBound_map_le

/-! ## Step 4b: specializations to the j-map and the Bezout family -/

def PjMap : Fin 2 → MvPolynomial (Fin 2) ℤ := ![jNumZ, jDenZ]

def NjMap : ℕ := max ((jNumZ.totalDegree + 1) ^ 2) ((jDenZ.totalDegree + 1) ^ 2)

def S_jMap : ℕ := max S_jNum S_jDen

lemma jMap_eq_map : jMap (K := K) = fun j => (PjMap j).map (Int.castRingHom K) := by
  funext j
  fin_cases j
  · simp [PjMap, jMap, jNumZ_map, jNumN_eq_jNum]
  · simp [PjMap, jMap, jDenZ_map, jDenN_eq_jDen]

lemma mulHeightBound_jMap_le :
    Height.mulHeightBound (jMap (K := K)) ≤ ((NjMap * S_jMap : ℕ) : ℝ) ^ Module.finrank ℚ K := by
  rw [jMap_eq_map]
  refine mulHeightBound_map_le PjMap NjMap S_jMap ?_ ?_
  · intro j
    fin_cases j
    · exact le_trans (support_card_le jNumZ jNumZ.totalDegree le_rfl) (le_max_left _ _)
    · exact le_trans (support_card_le jDenZ jDenZ.totalDegree le_rfl) (le_max_right _ _)
  · intro j s
    fin_cases j
    · exact le_trans (coeffAbsSum_coeff_le jNumZ s)
        (le_trans coeffAbsSum_jNumZ_le (le_max_left _ _))
    · exact le_trans (coeffAbsSum_coeff_le jDenZ s)
        (le_trans coeffAbsSum_jDenZ_le (le_max_right _ _))

def QZ : Fin 2 × Fin 2 → MvPolynomial (Fin 2) ℤ :=
  fun a => if a.1 = 0 then (if a.2 = 0 then jQ00Z else jQ01Z)
    else (if a.2 = 0 then jQ10Z else jQ11Z)

def NQ : ℕ := max (max ((jQ00Z.totalDegree + 1) ^ 2) ((jQ01Z.totalDegree + 1) ^ 2))
  (max ((jQ10Z.totalDegree + 1) ^ 2) ((jQ11Z.totalDegree + 1) ^ 2))

lemma QK_eq_map : QK (K := K) = fun a => (QZ a).map (Int.castRingHom K) := by
  funext a
  unfold QK QZ
  by_cases h1 : a.1 = 0 <;> by_cases h2 : a.2 = 0 <;>
    simp [h1, h2, jQ00Z_map, jQ01Z_map, jQ10Z_map, jQ11Z_map]

lemma mulHeightBound_QK_le :
    Height.mulHeightBound (QK (K := K)) ≤ ((NQ * S_Q : ℕ) : ℝ) ^ Module.finrank ℚ K := by
  rw [QK_eq_map]
  refine mulHeightBound_map_le QZ NQ S_Q ?_ ?_
  · intro a
    unfold QZ
    by_cases h1 : a.1 = 0 <;> by_cases h2 : a.2 = 0 <;>
      simp only [h1, h2, if_true, if_false]
    · exact le_trans (support_card_le jQ00Z jQ00Z.totalDegree le_rfl)
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact le_trans (support_card_le jQ01Z jQ01Z.totalDegree le_rfl)
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact le_trans (support_card_le jQ10Z jQ10Z.totalDegree le_rfl)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (support_card_le jQ11Z jQ11Z.totalDegree le_rfl)
        (le_trans (le_max_right _ _) (le_max_right _ _))
  · intro a s
    unfold QZ
    by_cases h1 : a.1 = 0 <;> by_cases h2 : a.2 = 0 <;>
      simp only [h1, h2, if_true, if_false]
    · exact le_trans (coeffAbsSum_coeff_le jQ00Z s) coeffAbsSum_jQ00Z_le
    · exact le_trans (coeffAbsSum_coeff_le jQ01Z s) coeffAbsSum_jQ01Z_le
    · exact le_trans (coeffAbsSum_coeff_le jQ10Z s) coeffAbsSum_jQ10Z_le
    · exact le_trans (coeffAbsSum_coeff_le jQ11Z s) coeffAbsSum_jQ11Z_le

#print axioms mulHeightBound_jMap_le
#print axioms mulHeightBound_QK_le

/-! ## Step 5: degree-bounded two-sided D3 comparison (route §6.3 D3) -/

def Cj : ℝ := max ((NjMap * S_jMap : ℕ) : ℝ) 1

def Cq : ℝ := max ((NQ * S_Q : ℕ) : ℝ) 1

def B_d (d : ℕ) : ℝ := max ((d : ℝ) * Real.log Cj) ((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq)

lemma one_le_Cj : 1 ≤ Cj := le_max_right _ _

lemma one_le_Cq : 1 ≤ Cq := le_max_right _ _

lemma mulHeightBound_jMap_le_pow (d : ℕ) (hd : Module.finrank ℚ K ≤ d) :
    Height.mulHeightBound (jMap (K := K)) ≤ Cj ^ d := by
  have h := mulHeightBound_jMap_le (K := K)
  have hbase : ((NjMap * S_jMap : ℕ) : ℝ) ≤ Cj := le_max_left _ _
  calc Height.mulHeightBound (jMap (K := K))
      ≤ ((NjMap * S_jMap : ℕ) : ℝ) ^ Module.finrank ℚ K := h
    _ ≤ Cj ^ Module.finrank ℚ K := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ ≤ Cj ^ d := pow_le_pow_right₀ one_le_Cj hd

lemma mulHeightBound_QK_le_pow (d : ℕ) (hd : Module.finrank ℚ K ≤ d) :
    Height.mulHeightBound (QK (K := K)) ≤ Cq ^ d := by
  have h := mulHeightBound_QK_le (K := K)
  have hbase : ((NQ * S_Q : ℕ) : ℝ) ≤ Cq := le_max_left _ _
  calc Height.mulHeightBound (QK (K := K))
      ≤ ((NQ * S_Q : ℕ) : ℝ) ^ Module.finrank ℚ K := h
    _ ≤ Cq ^ Module.finrank ℚ K := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ ≤ Cq ^ d := pow_le_pow_right₀ one_le_Cq hd

lemma jHeight_upper_deg (d : ℕ) (hd : Module.finrank ℚ K ≤ d) (lam : K) :
    jHeight lam ≤ (d : ℝ) * Real.log Cj + 6 * lambdaHeight lam := by
  have hle := Height.logHeight_eval_le (K := K) (N := 6) (p := jMap (K := K))
    jMap_isHomogeneous ![lam, 1]
  have hlog : Real.log (max (Height.mulHeightBound (jMap (K := K))) 1)
      ≤ (d : ℝ) * Real.log Cj := by
    have hmax : max (Height.mulHeightBound (jMap (K := K))) 1 ≤ Cj ^ d :=
      max_le (mulHeightBound_jMap_le_pow (K := K) d hd) (by simpa using pow_le_pow_right₀ one_le_Cj (Nat.zero_le d))
    have hpos1 : (0 : ℝ) < max (Height.mulHeightBound (jMap (K := K))) 1 := by positivity
    have hpos2 : (0 : ℝ) < Cj ^ d := pow_pos (lt_of_lt_of_le zero_lt_one one_le_Cj) d
    calc Real.log (max (Height.mulHeightBound (jMap (K := K))) 1)
        ≤ Real.log (Cj ^ d) := Real.log_le_log hpos1 hmax
      _ = (d : ℝ) * Real.log Cj := by
          rw [Real.log_pow]
  have hleft : Height.logHeight (fun j : Fin 2 => (jMap (K := K) j).eval ![lam, 1])
      = jHeight lam := by
    have hfun : (fun j : Fin 2 => (jMap (K := K) j).eval ![lam, 1])
        = ![(jNum (K := K)).eval ![lam, 1], (jDen (K := K)).eval ![lam, 1]] := by
      funext j
      fin_cases j <;> simp [jMap]
    rw [hfun, jHeight, legendreJ_eq_div, Height.logHeight₁_div_eq_logHeight]
  have hright : Height.logHeight (![lam, 1] : Fin 2 → K) = lambdaHeight lam :=
    (Height.logHeight₁_eq_logHeight lam).symm
  rw [hleft, hright] at hle
  calc jHeight lam ≤ Real.log (max (Height.mulHeightBound (jMap (K := K))) 1) + 6 * lambdaHeight lam := hle
    _ ≤ (d : ℝ) * Real.log Cj + 6 * lambdaHeight lam := add_le_add hlog (le_refl _)

lemma jHeight_lower_deg (d : ℕ) (hd : Module.finrank ℚ K ≤ d) (lam : K) :
    6 * lambdaHeight lam - ((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq) ≤ jHeight lam := by
  have hge := Height.logHeight_eval_ge (K := K) (M := 4) (N := 6) (q := QK (K := K))
    QK_isHomogeneous (p := pN (K := K)) (x := ![lam, 1]) (h := jBezN_relation ![lam, 1])
  have hcard : ((Nat.card (Fin 2) : ℝ) ^ Height.totalWeight K)
      = (2 : ℝ) ^ Module.finrank ℚ K := by
    rw [NumberField.totalWeight_eq_finrank]
    norm_num [Nat.card_fin]
  have hmax : max (Height.mulHeightBound (QK (K := K))) 1 ≤ Cq ^ d :=
    max_le (mulHeightBound_QK_le_pow (K := K) d hd) (by simpa using pow_le_pow_right₀ one_le_Cq (Nat.zero_le d))
  have hprod : ((Nat.card (Fin 2) : ℝ) ^ Height.totalWeight K)
      * max (Height.mulHeightBound (QK (K := K))) 1 ≤ (2 : ℝ) ^ d * Cq ^ d := by
    rw [hcard]
    refine mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hd) hmax ?_ ?_
    · exact le_trans zero_le_one (le_max_right _ _)
    · positivity
  have hlog : Real.log (((Nat.card (Fin 2) : ℝ) ^ Height.totalWeight K)
      * max (Height.mulHeightBound (QK (K := K))) 1)
      ≤ (d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq := by
    have hcard2 : ((Nat.card (Fin 2) : ℝ)) = 2 := by norm_num [Nat.card_fin]
    have hpos1 : (0 : ℝ) < ((Nat.card (Fin 2) : ℝ) ^ Height.totalWeight K)
        * max (Height.mulHeightBound (QK (K := K))) 1 := by
      rw [hcard2]
      exact mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) _)
        (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    calc Real.log (((Nat.card (Fin 2) : ℝ) ^ Height.totalWeight K)
          * max (Height.mulHeightBound (QK (K := K))) 1)
        ≤ Real.log ((2 : ℝ) ^ d * Cq ^ d) := Real.log_le_log hpos1 hprod
      _ = (d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq := by
          rw [Real.log_mul (pow_ne_zero d (by norm_num : (2:ℝ) ≠ 0))
            (pow_ne_zero d (ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_Cq)))]
          rw [Real.log_pow, Real.log_pow]
  have hpfun : (fun j : Fin 2 => (pN (K := K) j).eval ![lam, 1])
      = (256 : K)⁻¹ • ![(jNumN (K := K)).eval ![lam, 1],
          (jDenN (K := K)).eval ![lam, 1]] := by
    funext j
    fin_cases j <;> simp [pN, Pi.smul_apply]
  have hscale : Height.logHeight ((256 : K)⁻¹ • ![(jNumN (K := K)).eval ![lam, 1],
        (jDenN (K := K)).eval ![lam, 1]])
      = Height.logHeight ![(jNumN (K := K)).eval ![lam, 1],
          (jDenN (K := K)).eval ![lam, 1]] :=
    Height.logHeight_smul_eq_logHeight _ (inv_ne_zero (by norm_num : (256 : K) ≠ 0))
  have hswap : Height.logHeight ![(jNumN (K := K)).eval ![lam, 1],
        (jDenN (K := K)).eval ![lam, 1]]
      = Height.logHeight ![((jNum (K := K)).eval ![lam, 1]),
          ((jDen (K := K)).eval ![lam, 1])] := by
    rw [jNumN_eq_jNum, jDenN_eq_jDen]
  have hright : Height.logHeight (fun j : Fin 2 => (pN (K := K) j).eval ![lam, 1]) = jHeight lam := by
    rw [hpfun, hscale, hswap]
    rw [(Height.logHeight₁_div_eq_logHeight ((jNum (K := K)).eval ![lam, 1])
      ((jDen (K := K)).eval ![lam, 1])).symm]
    rw [← legendreJ_eq_div (K := K) lam, jHeight]
  have hleft : Height.logHeight (![lam, 1] : Fin 2 → K) = lambdaHeight lam :=
    (Height.logHeight₁_eq_logHeight lam).symm
  rw [hleft, hright] at hge
  have hb : -((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq)
      ≤ -Real.log (((Nat.card (Fin 2) : ℝ) ^ Height.totalWeight K)
        * max (Height.mulHeightBound (QK (K := K))) 1) := neg_le_neg hlog
  calc 6 * lambdaHeight lam - ((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq)
      = -((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq) + 6 * lambdaHeight lam := by ring
    _ ≤ -Real.log (((Nat.card (Fin 2) : ℝ) ^ Height.totalWeight K)
        * max (Height.mulHeightBound (QK (K := K))) 1) + 6 * lambdaHeight lam :=
        add_le_add hb (le_refl _)
    _ ≤ jHeight lam := hge

/-- **D3 (route §6.3)**: degree-bounded two-sided height comparison
`|h(j(lam)) - 6 h(lam)| <= B_d`, uniformly for all number fields of degree at most `d`
and all `lam`. This does not require `lam` to satisfy the Kv condition. -/
theorem jHeight_relation_deg (d : ℕ) :
    ∃ B : ℝ, ∀ (K : Type*) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ d → ∀ lam : K, |jHeight lam - 6 * lambdaHeight lam| ≤ B := by
  refine ⟨B_d d, ?_⟩
  intro K _ _ hd lam
  have hup := jHeight_upper_deg (K := K) d hd lam
  have hlow := jHeight_lower_deg (K := K) d hd lam
  rw [abs_le]
  constructor
  · have h1 : -((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq)
        ≤ jHeight lam - 6 * lambdaHeight lam := by
      calc -((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq)
          = (6 * lambdaHeight lam - ((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq))
            - 6 * lambdaHeight lam := by ring
        _ ≤ jHeight lam - 6 * lambdaHeight lam := sub_le_sub_right hlow _
    have h2 : -(B_d d) ≤ -((d : ℝ) * Real.log 2 + (d : ℝ) * Real.log Cq) := by
      unfold B_d
      exact neg_le_neg (le_max_right _ _)
    exact le_trans h2 h1
  · have h1 : jHeight lam - 6 * lambdaHeight lam ≤ (d : ℝ) * Real.log Cj := by
      have h := sub_le_iff_le_add.mpr hup
      exact h
    exact le_trans h1 (le_max_left _ _)

#print axioms jHeight_relation_deg

/-! ## Step 6 (D1a): the actual height dictionary (D3) with q-height = j-height -/

/-- The q-height of the initial Theta-data is the actual j-height `jHeight`, and
the standard height differs from `jHeight / 6` by an explicit degree-bounded
constant. This discharges the (D3) dictionary field of `D1AnalyticInput` with the
actual height function (route section 6.3). -/
theorem height_dictionary_deg (d : ℕ) :
    ∃ B : ℝ, ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℚ K ≤ d →
      ∀ lam : K, |lambdaHeight lam - jHeight lam / 6| ≤ B := by
  obtain ⟨B, hB⟩ := jHeight_relation_deg d
  refine ⟨B / 6, fun K _ _ hd lam => ?_⟩
  have h := hB (K := K) hd lam
  have h1 : lambdaHeight lam - jHeight lam / 6
      = -((jHeight lam - 6 * lambdaHeight lam) / 6) := by ring
  rw [h1, abs_neg, abs_div]
  have h6 : |(6 : ℝ)| = 6 := by norm_num
  rw [h6]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- Inhabitant of the old (D3) interface with the actual q-height `jHeight`. -/
theorem heightDictionaryInterface_jHeight (d : ℕ) :
    ∃ B : ℝ, ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℚ K ≤ d →
      HeightDictionaryInterface (K := K) (jHeight (K := K)) B := by
  obtain ⟨B, hB⟩ := height_dictionary_deg d
  exact ⟨B, fun K _ _ hd => hB (K := K) hd⟩

#print axioms height_dictionary_deg
#print axioms heightDictionaryInterface_jHeight

end LeanFormal.IUT.XiFPaper.G1JHeightUniformActual
end