import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field
abbrev G := F ≃ₐ[ℚ] F

/-! ## 1. The cubic, its derivative, and separability -/

theorem S1687P_natDegree : S1687P.natDegree = 3 := by
  unfold S1687P
  compute_degree!

theorem S1687P_ne_zero : S1687P ≠ 0 := by
  intro h
  have hdeg := S1687P_natDegree
  rw [h, Polynomial.natDegree_zero] at hdeg
  norm_num at hdeg

def S1687Pderiv : ℚ[X] :=
  C 1391569403904 * X ^ 2 + C 7947904090112 * X + C 1991485440000

def S1687PCertA : ℚ[X] :=
  C (92045312/3327590340912772265625 : ℚ) * X +
    C (47671697641/269534817613934553515625 : ℚ)

def S1687PCertB : ℚ[X] :=
  C (-92045312/9982771022738316796875 : ℚ) * X ^ 2 +
    C (-22987702883/269534817613934553515625 : ℚ) * X +
    C (-2468003/55631877699504960000 : ℚ)

theorem S1687P_derivative : derivative S1687P = S1687Pderiv := by
  unfold S1687P S1687Pderiv
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_C, derivative_X]
  norm_num
  simp only [← mul_assoc, ← C_mul]
  norm_num

theorem S1687P_bezout_eval {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (x : K) :
    aeval x S1687PCertA * aeval x S1687P +
      aeval x S1687PCertB * aeval x S1687Pderiv = 1 := by
  unfold S1687PCertA S1687PCertB S1687P S1687Pderiv
  simp only [aeval_add, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

theorem S1687P_bezout : S1687PCertA * S1687P + S1687PCertB * S1687Pderiv = 1 := by
  have h := S1687P_bezout_eval (K := RatFunc ℚ) (RatFunc.X : RatFunc ℚ)
  have hX : (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) X = RatFunc.X := by
    change algebraMap ℚ[X] (RatFunc ℚ) X = RatFunc.X
    exact RatFunc.algebraMap_X
  have hmap : ∀ p : ℚ[X],
      Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X) p =
        algebraMap ℚ[X] (RatFunc ℚ) p := by
    intro p
    rw [← hX,
      Polynomial.eval₂_algebraMap_X p
        (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ))]
    rfl
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  simpa [Polynomial.aeval_def, hmap] using h

theorem S1687P_separable : S1687P.Separable := by
  rw [separable_def']
  refine ⟨S1687PCertA, S1687PCertB, ?_⟩
  rw [S1687P_derivative]
  exact S1687P_bezout

/-! ## 2. S1687P splits in F' -/

theorem S1687P_splits_F : (S1687P.map (algebraMap ℚ F)).Splits := by
  let Ω := AlgebraicClosure F
  have hH : (S1687H.map (algebraMap ℚ F)).Splits := S1687H_splits_in_F'
  have hHne : (S1687H.map (algebraMap ℚ F)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective]
    exact S1687H_ne_zero
  have hPneΩ : (S1687P.map (algebraMap ℚ Ω)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ Ω).injective]
    exact S1687P_ne_zero
  have hmapP : ((S1687P.map (algebraMap ℚ F)).map (algebraMap F Ω)) =
      S1687P.map (algebraMap ℚ Ω) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ F Ω]
  have hmapH : ((S1687H.map (algebraMap ℚ F)).map (algebraMap F Ω)) =
      S1687H.map (algebraMap ℚ Ω) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ F Ω]
  have hroots : ∀ x ∈ ((S1687P.map (algebraMap ℚ F)).map (algebraMap F Ω)).roots,
      x ∈ (algebraMap F Ω).range := by
    intro x hx
    have hx'' : x ∈ (S1687P.map (algebraMap ℚ Ω)).roots := by
      rwa [hmapP] at hx
    have hxroot : aeval x S1687P = 0 := by
      have h : (S1687P.map (algebraMap ℚ Ω)).IsRoot x := (Polynomial.mem_roots hPneΩ).mp hx''
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using h
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x (by norm_num : 0 < 2)
    have hyH : aeval y S1687H = 0 := by
      rw [S1687H_eval_eq, hy]
      exact hxroot
    have hyroot : ((S1687H.map (algebraMap ℚ F)).map (algebraMap F Ω)).IsRoot y := by
      rw [hmapH]
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hyH
    have hy_range : y ∈ (algebraMap F Ω).range :=
      Polynomial.Splits.mem_range_of_isRoot hH hHne hyroot
    obtain ⟨z, hz⟩ := hy_range
    refine ⟨z ^ 2, ?_⟩
    rw [map_pow, hz, hy]
  apply Polynomial.Splits.of_splits_map (i := algebraMap F Ω)
  · exact IsAlgClosed.splits _
  · intro x hx
    have hx' : x ∈ (S1687P.map (algebraMap ℚ Ω)).roots := by
      rwa [hmapP] at hx
    exact hroots x (by rwa [hmapP])

theorem S1687P_card_rootSet : Nat.card (S1687P.rootSet F) = 3 := by
  have h := Polynomial.card_rootSet_eq_natDegree (K := F) S1687P_separable S1687P_splits_F
  rw [S1687P_natDegree] at h
  exact Nat.card_eq_fintype_card.trans h

/-! ## 3. Choosing square roots -/

theorem S1687H_eq_comp : S1687H = S1687P.comp (X ^ 2) := by
  unfold S1687H S1687P
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.X_pow_comp]
  ring_nf

theorem sqrt_poly_splits (c : S1687P.rootSet F) :
    ((X ^ 2 - C (c : F)) : F[X]).Splits := by
  have hH : (S1687H.map (algebraMap ℚ F)).Splits := S1687H_splits_in_F'
  have hHne : (S1687H.map (algebraMap ℚ F)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective]
    exact S1687H_ne_zero
  have hc : aeval (c : F) S1687P = 0 :=
    (Polynomial.mem_rootSet_of_ne S1687P_ne_zero).mp c.2
  have hlin : (X - C (c : F)) ∣ S1687P.map (algebraMap ℚ F) :=
    Polynomial.dvd_iff_isRoot.mpr (by
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hc)
  have hcomp : ((X - C (c : F)).comp (X ^ 2)) ∣
      ((S1687P.map (algebraMap ℚ F)).comp (X ^ 2)) := by
    rcases hlin with ⟨q, hq⟩
    refine ⟨q.comp (X ^ 2), ?_⟩
    rw [hq, Polynomial.mul_comp]
  have hleft : (X - C (c : F)).comp (X ^ 2) = X ^ 2 - C (c : F) := by
    simp [Polynomial.sub_comp]
  have hright : (S1687P.map (algebraMap ℚ F)).comp (X ^ 2) =
      S1687H.map (algebraMap ℚ F) := by
    rw [S1687H_eq_comp, Polynomial.map_comp]
    simp
  rw [hleft, hright] at hcomp
  exact Polynomial.Splits.of_dvd hH hHne hcomp

theorem sqrt_exists (c : S1687P.rootSet F) :
    ∃ r : F, r ^ 2 = (c : F) := by
  have hs := sqrt_poly_splits c
  have hmonic : ((X ^ 2 - C (c : F)) : F[X]).Monic :=
    monic_X_pow_sub_C (c : F) (by norm_num : (2:ℕ) ≠ 0)
  have hdeg : ((X ^ 2 - C (c : F)) : F[X]).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, natDegree_X_pow_sub_C]
    norm_num
  let r := Polynomial.rootOfSplits hs hdeg
  have hr : Polynomial.eval r (X ^ 2 - C (c : F)) = 0 :=
    Polynomial.eval_rootOfSplits hs hdeg
  refine ⟨r, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  linear_combination hr

noncomputable def r (c : S1687P.rootSet F) : F :=
  Classical.choose (sqrt_exists c)

theorem r_sq (c : S1687P.rootSet F) : (r c) ^ 2 = (c : F) :=
  Classical.choose_spec (sqrt_exists c)

noncomputable def iroot : F := Classical.choose S1720HasSqrtNegOne

theorem iroot_sq : iroot ^ 2 = (-1 : F) := by
  have h : iroot * iroot = -1 := Classical.choose_spec S1720HasSqrtNegOne
  rw [sq]
  exact h

theorem S1720SqrtPolynomial_ne_zero : S1720SqrtPolynomial ≠ 0 := by
  unfold S1720SqrtPolynomial
  intro h
  have h0 := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simp at h0

theorem S1720H_ne_zero : S1720H ≠ 0 := by
  unfold S1720H
  exact mul_ne_zero S1687H_ne_zero S1720SqrtPolynomial_ne_zero

/-! ## 4. Roots of S1720H and generation -/

theorem root_decomp {x : F} (hx : x ∈ S1720H.rootSet F) :
    (∃ c : S1687P.rootSet F, x = r c ∨ x = - r c) ∨ x = iroot ∨ x = -iroot := by
  have hx_eval : aeval x S1720H = 0 :=
    (Polynomial.mem_rootSet_of_ne S1720H_ne_zero).mp hx
  have hx_eval' : aeval x (S1687H * S1720SqrtPolynomial) = 0 := by
    simpa [S1720H] using hx_eval
  rw [Polynomial.aeval_mul (R := ℚ) (x := x)] at hx_eval'
  rcases mul_eq_zero.mp hx_eval' with hH | hI
  · left
    have hx2 : aeval (x ^ 2) S1687P = 0 := by
      rw [← S1687H_eval_eq]
      exact hH
    have hx2mem : x ^ 2 ∈ S1687P.rootSet F :=
      (Polynomial.mem_rootSet_of_ne S1687P_ne_zero).mpr hx2
    let c : S1687P.rootSet F := ⟨x ^ 2, hx2mem⟩
    refine ⟨c, ?_⟩
    have hc : (c : F) = x ^ 2 := rfl
    have hsq : x ^ 2 = (r c) ^ 2 := by rw [← hc, r_sq c]
    exact eq_or_eq_neg_of_sq_eq_sq x (r c) hsq
  · right
    have hx2 : x ^ 2 = (-1 : F) := by
      have h : aeval x S1720SqrtPolynomial = 0 := hI
      unfold S1720SqrtPolynomial at h
      simp only [map_add, map_pow, aeval_X, aeval_one] at h
      linear_combination h
    have hsq : x ^ 2 = iroot ^ 2 := by rw [hx2, iroot_sq]
    exact eq_or_eq_neg_of_sq_eq_sq x iroot hsq

theorem eq_of_agrees_on_generators (σ τ : G)
    (h : ∀ c : S1687P.rootSet F, σ (r c) = τ (r c))
    (hi : σ iroot = τ iroot) : σ = τ := by
  have hroot : ∀ x ∈ S1720H.rootSet F, σ x = τ x := by
    intro x hx
    rcases root_decomp hx with ⟨c, hx' | hx'⟩ | hx' | hx'
    · rw [hx', h c]
    · rw [hx']
      simp [h c]
    · rw [hx', hi]
    · rw [hx']
      simp [hi]
  have hgen : Algebra.adjoin ℚ (S1720H.rootSet F) = ⊤ :=
    Polynomial.SplittingField.adjoin_rootSet (f := S1720H)
  have heq : σ.toAlgHom = τ.toAlgHom :=
    AlgHom.ext_of_adjoin_eq_top hgen (fun x hx => hroot x hx)
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun heq x

/-! ## 5. The action on roots of S1687P and its kernel -/

abbrev φ : G →* Equiv.Perm (S1687P.rootSet F) :=
  MulAction.toPermHom G (S1687P.rootSet F)

abbrev K : Subgroup G := φ.ker

theorem K_apply_root (σ : K) (c : S1687P.rootSet F) :
    (σ : G) (c : F) = (c : F) := by
  have h : φ (σ : G) = 1 := σ.2
  have hc : ((σ : G) • c : S1687P.rootSet F) = c :=
    congrArg (fun f : Equiv.Perm (S1687P.rootSet F) => f c) h
  have hc' : (σ : G) • (c : F) = (c : F) := by
    rw [← Polynomial.rootSet.coe_smul (σ : G) c]
    exact congrArg Subtype.val hc
  simpa using hc'

theorem root_sign (σ : K) (c : S1687P.rootSet F) :
    (σ : G) (r c) = r c ∨ (σ : G) (r c) = - r c := by
  have hsq : ((σ : G) (r c)) ^ 2 = (r c) ^ 2 := by
    rw [← map_pow, r_sq c, K_apply_root σ c]
  exact eq_or_eq_neg_of_sq_eq_sq _ _ hsq

theorem i_sign (σ : K) :
    (σ : G) iroot = iroot ∨ (σ : G) iroot = - iroot := by
  have hsq : ((σ : G) iroot) ^ 2 = iroot ^ 2 := by
    rw [← map_pow, iroot_sq]
    simp
  exact eq_or_eq_neg_of_sq_eq_sq _ _ hsq

def sgn (σ : K) (c : S1687P.rootSet F) : Bool := by
  classical
  exact decide ((σ : G) (r c) = r c)

def sgnI (σ : K) : Bool := by
  classical
  exact decide ((σ : G) iroot = iroot)

def signFun (σ : K) : (S1687P.rootSet F → Bool) × Bool :=
  (sgn σ, sgnI σ)

theorem sgn_eq_apply_r (σ τ : K) (c : S1687P.rootSet F)
    (h : sgn σ c = sgn τ c) :
    (σ : G) (r c) = (τ : G) (r c) := by
  by_cases hσ : (σ : G) (r c) = r c
  · have hσb : sgn σ c = true := by simp [sgn, hσ]
    have hτb : sgn τ c = true := by rw [← h]; exact hσb
    have hτ : (τ : G) (r c) = r c := by
      by_contra hτne
      have : sgn τ c = false := by simp [sgn, hτne]
      rw [this] at hτb
      simp at hτb
    rw [hσ, hτ]
  · have hτne : ¬ (τ : G) (r c) = r c := by
      intro hτ
      have hτb : sgn τ c = true := by simp [sgn, hτ]
      have hσb : sgn σ c = true := by rw [h]; exact hτb
      simp [sgn, hσ] at hσb
    have hσneg : (σ : G) (r c) = - r c := (root_sign σ c).resolve_left hσ
    have hτneg : (τ : G) (r c) = - r c := (root_sign τ c).resolve_left hτne
    rw [hσneg, hτneg]

theorem sgnI_eq_apply_i (σ τ : K) (h : sgnI σ = sgnI τ) :
    (σ : G) iroot = (τ : G) iroot := by
  by_cases hσ : (σ : G) iroot = iroot
  · have hσb : sgnI σ = true := by simp [sgnI, hσ]
    have hτb : sgnI τ = true := by rw [← h]; exact hσb
    have hτ : (τ : G) iroot = iroot := by
      by_contra hτne
      have : sgnI τ = false := by simp [sgnI, hτne]
      rw [this] at hτb
      simp at hτb
    rw [hσ, hτ]
  · have hτne : ¬ (τ : G) iroot = iroot := by
      intro hτ
      have hτb : sgnI τ = true := by simp [sgnI, hτ]
      have hσb : sgnI σ = true := by rw [h]; exact hτb
      simp [sgnI, hσ] at hσb
    have hσneg : (σ : G) iroot = - iroot := (i_sign σ).resolve_left hσ
    have hτneg : (τ : G) iroot = - iroot := (i_sign τ).resolve_left hτne
    rw [hσneg, hτneg]

theorem signFun_injective : Function.Injective signFun := by
  intro σ τ h
  apply Subtype.ext
  apply eq_of_agrees_on_generators
  · intro c
    exact sgn_eq_apply_r σ τ c (congrFun (congrArg Prod.fst h) c)
  · exact sgnI_eq_apply_i σ τ (congrArg Prod.snd h)

theorem K_sq_one (σ : K) : σ * σ = 1 := by
  apply Subtype.ext
  apply eq_of_agrees_on_generators
  · intro c
    change (σ : G) ((σ : G) (r c)) = (1 : G) (r c)
    rcases root_sign σ c with hs | hs
    · simp [hs]
    · rw [hs]
      simp [hs]
  · change (σ : G) ((σ : G) iroot) = (1 : G) iroot
    rcases i_sign σ with hs | hs
    · simp [hs]
    · rw [hs]
      simp [hs]

theorem K_isPGroup : IsPGroup 2 K := by
  intro σ
  refine ⟨1, ?_⟩
  simpa [pow_two] using K_sq_one σ

theorem K_card_le_16 : Nat.card K ≤ 16 := by
  have hcod : Nat.card ((S1687P.rootSet F → Bool) × Bool) = 16 := by
    rw [Nat.card_prod, Nat.card_fun, S1687P_card_rootSet]
    norm_num
  have hle := Nat.card_le_card_of_injective signFun signFun_injective
  rwa [hcod] at hle

theorem K_card_dvd_16 : Nat.card K ∣ 16 := by
  have hK : IsPGroup 2 K := K_isPGroup
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := K)).mp hK
  have hnle : n ≤ 4 := by
    have hle : 2 ^ n ≤ 2 ^ 4 := by
      rw [← hn]
      simpa using K_card_le_16
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  rw [hn, show (16 : ℕ) = 2 ^ 4 by norm_num]
  exact pow_dvd_pow 2 hnle

theorem image_card_dvd_6 : Nat.card φ.range ∣ 6 := by
  have h1 : Nat.card φ.range ∣ Nat.card (Equiv.Perm (S1687P.rootSet F)) :=
    Subgroup.card_subgroup_dvd_card φ.range
  have h2 : Nat.card (Equiv.Perm (S1687P.rootSet F)) = Nat.factorial 3 := by
    rw [Nat.card_perm, S1687P_card_rootSet]
  rw [h2] at h1
  norm_num at h1 ⊢
  exact h1

/-! ## 6. The degree bound and coprimality -/

theorem S1722_finrank_dvd_96 : Module.finrank ℚ F ∣ 96 := by
  have hgal : Nat.card G = Module.finrank ℚ F :=
    IsGalois.card_aut_eq_finrank ℚ F
  have hcard : Nat.card G = Nat.card K * Nat.card φ.range := by
    rw [← (φ.ker).card_mul_index, Subgroup.index_ker φ]
  have h96 : Nat.card G ∣ 96 := by
    rw [hcard]
    have h := mul_dvd_mul K_card_dvd_16 image_card_dvd_6
    norm_num at h ⊢
    exact h
  rwa [hgal] at h96

theorem S1722_finrank_prime_factors_le_three :
    ∀ p : ℕ, p.Prime → p ∣ Module.finrank ℚ F → p ≤ 3 := by
  intro p hp hpdvd
  have h96 : p ∣ 96 := hpdvd.trans S1722_finrank_dvd_96
  have hdiv' : p ∣ 2 ^ 5 * 3 := by
    norm_num at h96 ⊢
    exact h96
  have h2or3 := hp.dvd_mul.mp hdiv'
  rcases h2or3 with h2 | h3
  · have h2' : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have hp2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    omega
  · exact Nat.le_of_dvd (by norm_num) h3

theorem coprime_96_primeGeFive (l : PrimeGeFive) : Nat.Coprime 96 l.value := by
  refine Nat.Coprime.symm ?_
  rw [Nat.Prime.coprime_iff_not_dvd l.prime]
  intro hdiv
  have hdiv' : l.value ∣ 2 ^ 5 * 3 := by
    norm_num at hdiv ⊢
    exact hdiv
  have h2or3 := l.prime.dvd_mul.mp hdiv'
  rcases h2or3 with h2 | h3
  · have h2' : l.value ∣ 2 := l.prime.dvd_of_dvd_pow h2
    have hle : l.value ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    have h5 := l.ge_five
    omega
  · have hle : l.value ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    have h5 := l.ge_five
    omega

theorem S1722DegreePrimeToL (l : PrimeGeFive) : S1720DegreePrimeToL l := by
  unfold S1720DegreePrimeToL
  exact (coprime_96_primeGeFive l).coprime_dvd_left S1722_finrank_dvd_96

noncomputable def S1722InitialThetaArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l :=
  S1720InitialThetaArithmeticData l (S1722DegreePrimeToL l)

theorem S1722PaperArithmeticData_of_torsion (l : PrimeGeFive)
    (htor : S1720Torsion23Missing) : S1720PaperArithmeticData l where
  degreePrimeToL := S1722DegreePrimeToL l
  torsion23 := htor

#print axioms S1687P_separable
#print axioms S1687P_splits_F
#print axioms S1687P_card_rootSet
#print axioms K_card_dvd_16
#print axioms image_card_dvd_6
#print axioms S1722_finrank_dvd_96
#print axioms S1722_finrank_prime_factors_le_three
#print axioms S1722DegreePrimeToL

end LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual
