import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# S1723: the degree of the actual S1667 field is at most 96

Let P = S1687P be the residual cubic of the 3-division polynomial of the
S1667 curve and let H = S1687H = P(X^2).  The actual paper field is

  F' = SplittingField (H * (X^2 + 1)),

which is S1720Field.

We prove [F' : Q] divides 96.  The proof is a tower estimate, not an assumed
degree:

* L0 = SplittingField P is the splitting field of the cubic P; a splitting
  field of a degree-n polynomial has degree dividing n!, so [L0 : Q] | 6.
* L = SplittingField (H.map L0) is obtained from L0 by adjoining the square
  roots of the three roots of P, together with i (the root of X^2 + 1).
  Over L0, every root x of H has x^2 a root of P, hence x^2 is in L0, so
  every L0-automorphism of L sends x to ±x; the same holds for i.  The
  roots generate L over L0, so the automorphism group embeds into the group
  of sign choices on the three roots of P and on i, i.e. into (Z/2)^4.
  In particular it is a 2-group of order at most 16, whence [L : L0] | 16.
* [F' : Q] divides [L : Q] = [L0 : Q] * [L : L0], because H * (X^2+1)
  splits in L and F' is its splitting field over Q.

Thus [F' : Q] | 6 * 16 = 96, and every prime divisor is at most 3.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1723DegreeBoundActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

/-! ## 1. The cubic, the sextic, and the field L0 -/

theorem S1687P_natDegree : S1687P.natDegree = 3 := by
  unfold S1687P
  compute_degree!

theorem S1687P_ne_zero : S1687P ≠ 0 := by
  intro h
  have hd := S1687P_natDegree
  rw [h, Polynomial.natDegree_zero] at hd
  norm_num at hd

/-- H = P(X^2). -/
theorem S1687H_eq_comp : S1687H = S1687P.comp (X ^ 2) := by
  unfold S1687H S1687P
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.X_pow_comp]
  ring_nf

theorem S1720SqrtPolynomial_ne_zero : S1720SqrtPolynomial ≠ 0 := by
  unfold S1720SqrtPolynomial
  intro h
  have h0 := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simp at h0

theorem S1720H_ne_zero : S1720H ≠ 0 := by
  unfold S1720H
  exact mul_ne_zero S1687H_ne_zero S1720SqrtPolynomial_ne_zero

/-- A splitting field of a degree-n polynomial over a characteristic-zero
field has degree dividing n!. -/
theorem splittingField_finrank_dvd_factorial
    (K : Type*) [Field K] [CharZero K] (p : K[X]) :
    Module.finrank K p.SplittingField ∣ p.natDegree.factorial := by
  classical
  let E := p.SplittingField
  haveI : Fact ((p.map (algebraMap K E)).Splits) := ⟨SplittingField.splits p⟩
  haveI : Normal K E := Polynomial.SplittingField.instNormal p
  haveI : IsGalois K E := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hgal : Nat.card p.Gal = Module.finrank K E := IsGalois.card_aut_eq_finrank K E
  rw [← hgal]
  let φ := Polynomial.Gal.galActionHom p E
  have hφ : Function.Injective φ := Polynomial.Gal.galActionHom_injective p E
  let G := φ.range
  have h1 : Nat.card p.Gal = Nat.card G := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [h1]
  have h2 : Nat.card G ∣ Nat.card (Equiv.Perm (p.rootSet E)) := Subgroup.card_subgroup_dvd_card G
  have h3 : Nat.card (Equiv.Perm (p.rootSet E)) = Nat.factorial (Nat.card (p.rootSet E)) :=
    Nat.card_perm
  rw [h3] at h2
  have hcard_le : Nat.card (p.rootSet E) ≤ p.natDegree := by
    rw [Nat.card_eq_fintype_card]
    have h := Polynomial.ncard_rootSet_le p E
    rwa [← Set.fintypeCard_eq_ncard] at h
  have hfac : Nat.factorial (Nat.card (p.rootSet E)) ∣ Nat.factorial p.natDegree :=
    Nat.factorial_dvd_factorial hcard_le
  exact dvd_trans h2 hfac

/-- The splitting field of the residual cubic. -/
abbrev L0 : Type := Polynomial.SplittingField S1687P

/-- [L0 : Q] divides 3! = 6. -/
theorem L0_finrank_dvd_six : Module.finrank ℚ L0 ∣ 6 := by
  have h := splittingField_finrank_dvd_factorial ℚ S1687P
  rw [S1687P_natDegree] at h
  norm_num at h
  exact h

/-! ## 2. The field L over L0 -/

/-- The field obtained from L0 by adjoining the roots of H and of X^2+1. -/
abbrev L : Type := Polynomial.SplittingField (S1720H.map (algebraMap ℚ L0))

theorem L_splits : ((S1720H.map (algebraMap ℚ L0)).map (algebraMap L0 L)).Splits :=
  SplittingField.splits (S1720H.map (algebraMap ℚ L0))

theorem L_map_ne_zero : (S1720H.map (algebraMap ℚ L0)).map (algebraMap L0 L) ≠ 0 := by
  rw [Polynomial.map_ne_zero_iff (algebraMap L0 L).injective,
    Polynomial.map_ne_zero_iff (algebraMap ℚ L0).injective]
  exact S1720H_ne_zero

/-- The same polynomial, but now over L. -/
theorem S1720H_splits_L : (S1720H.map (algebraMap ℚ L)).Splits := by
  have h := L_splits
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ L0 L] at h

/-- The roots of the cubic P in L0. -/
abbrev RootP : Type := S1687P.rootSet L0

theorem RootP_card_le_three : Nat.card RootP ≤ 3 := by
  rw [Nat.card_eq_fintype_card]
  have h := Polynomial.ncard_rootSet_le S1687P L0
  rw [← Set.fintypeCard_eq_ncard] at h
  simpa [S1687P_natDegree] using h

/-! ## 3. Square roots of the roots of P and a square root of -1 -/

theorem S1687P_map_ne_zero : (S1687P.map (algebraMap ℚ L0)) ≠ 0 := by
  rw [Polynomial.map_ne_zero_iff (algebraMap ℚ L0).injective]
  exact S1687P_ne_zero

theorem S1687P_map_comp_eq :
    (S1687P.map (algebraMap ℚ L0)).comp (X ^ 2) = S1687H.map (algebraMap ℚ L0) := by
  rw [S1687H_eq_comp, Polynomial.map_comp]
  simp

/-- For every root c of P in L0, the quadratic X^2 - c splits in L. -/
theorem sqrt_splits (c : RootP) :
    (((X ^ 2 - C (c : L0)) : L0[X]).map (algebraMap L0 L)).Splits := by
  have hc : aeval (c : L0) S1687P = 0 :=
    (Polynomial.mem_rootSet_of_ne S1687P_ne_zero).mp c.2
  have hlin : (X - C (c : L0)) ∣ S1687P.map (algebraMap ℚ L0) :=
    Polynomial.dvd_iff_isRoot.mpr (by
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hc)
  have hcomp : ((X - C (c : L0)).comp (X ^ 2)) ∣
      ((S1687P.map (algebraMap ℚ L0)).comp (X ^ 2)) := by
    rcases hlin with ⟨q, hq⟩
    exact ⟨q.comp (X ^ 2), by rw [hq, Polynomial.mul_comp]⟩
  have hleft : ((X - C (c : L0)).comp (X ^ 2)) = (X ^ 2 - C (c : L0) : L0[X]) := by
    simp [Polynomial.sub_comp]
  have hdvdH : (X ^ 2 - C (c : L0) : L0[X]) ∣ S1687H.map (algebraMap ℚ L0) := by
    rw [← hleft, ← S1687P_map_comp_eq]
    exact hcomp
  have hdvd : (X ^ 2 - C (c : L0) : L0[X]) ∣ S1720H.map (algebraMap ℚ L0) := by
    rw [S1720H, Polynomial.map_mul]
    exact dvd_mul_of_dvd_left hdvdH _
  have hmapdvd : (((X ^ 2 - C (c : L0)) : L0[X]).map (algebraMap L0 L)) ∣
      (S1720H.map (algebraMap ℚ L0)).map (algebraMap L0 L) :=
    Polynomial.map_dvd _ hdvd
  exact Polynomial.Splits.of_dvd L_splits L_map_ne_zero hmapdvd

theorem sqrt_map_natDegree (c : RootP) :
    (((X ^ 2 - C (c : L0)) : L0[X]).map (algebraMap L0 L)).natDegree = 2 := by
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap L0 L).injective,
    Polynomial.natDegree_X_pow_sub_C]

theorem sqrt_map_degree_ne_zero (c : RootP) :
    (((X ^ 2 - C (c : L0)) : L0[X]).map (algebraMap L0 L)).degree ≠ 0 := by
  have hne : (((X ^ 2 - C (c : L0)) : L0[X]).map (algebraMap L0 L)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap L0 L).injective]
    exact (monic_X_pow_sub_C (c : L0) (by norm_num : (2 : ℕ) ≠ 0)).ne_zero
  rw [Polynomial.degree_eq_natDegree hne, sqrt_map_natDegree c]
  norm_num

/-- A chosen square root in L of a root c of P. -/
noncomputable def beta (c : RootP) : L :=
  Polynomial.rootOfSplits (sqrt_splits c) (sqrt_map_degree_ne_zero c)

theorem beta_sq (c : RootP) : (beta c) ^ 2 = algebraMap L0 L (c : L0) := by
  have hr := Polynomial.eval_rootOfSplits (sqrt_splits c) (sqrt_map_degree_ne_zero c)
  rw [Polynomial.eval_map] at hr
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at hr
  unfold beta
  linear_combination hr

/-- The polynomial X^2 + 1 splits in L. -/
theorem i_splits : (((X ^ 2 + 1) : L0[X]).map (algebraMap L0 L)).Splits := by
  have hdvd : ((X ^ 2 + 1) : L0[X]) ∣ S1720H.map (algebraMap ℚ L0) := by
    change ((X ^ 2 + 1) : L0[X]) ∣
      (S1687H * S1720SqrtPolynomial).map (algebraMap ℚ L0)
    rw [Polynomial.map_mul]
    have h : (S1720SqrtPolynomial.map (algebraMap ℚ L0)) = (X ^ 2 + 1 : L0[X]) := by
      simp [S1720SqrtPolynomial]
    rw [h]
    exact dvd_mul_left (X ^ 2 + 1 : L0[X]) (S1687H.map (algebraMap ℚ L0))
  have hmapdvd : (((X ^ 2 + 1) : L0[X]).map (algebraMap L0 L)) ∣
      (S1720H.map (algebraMap ℚ L0)).map (algebraMap L0 L) :=
    Polynomial.map_dvd _ hdvd
  exact Polynomial.Splits.of_dvd L_splits L_map_ne_zero hmapdvd

theorem i_map_natDegree : (((X ^ 2 + 1) : L0[X]).map (algebraMap L0 L)).natDegree = 2 := by
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap L0 L).injective]
  compute_degree!

theorem i_map_degree_ne_zero : (((X ^ 2 + 1) : L0[X]).map (algebraMap L0 L)).degree ≠ 0 := by
  have hne : (((X ^ 2 + 1) : L0[X]).map (algebraMap L0 L)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap L0 L).injective]
    intro h
    have h0 := congrArg (fun p : L0[X] => p.coeff 0) h
    simp at h0
  rw [Polynomial.degree_eq_natDegree hne, i_map_natDegree]
  norm_num

/-- A chosen square root of -1 in L. -/
noncomputable def iroot : L :=
  Polynomial.rootOfSplits i_splits i_map_degree_ne_zero

theorem iroot_sq : (iroot) ^ 2 = (-1 : L) := by
  have hr := Polynomial.eval_rootOfSplits i_splits i_map_degree_ne_zero
  rw [Polynomial.eval_map] at hr
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one] at hr
  unfold iroot
  linear_combination hr

/-! ## 4. The roots of H * (X^2+1) generate L, and decompose into
± beta c and ± i -/

theorem root_mem_adjoin (x : L)
    (hx : x ∈ (S1720H.map (algebraMap ℚ L0)).rootSet L) :
    x ∈ Algebra.adjoin L0 (Set.range beta ∪ {iroot}) := by
  have hL0ne : (S1720H.map (algebraMap ℚ L0)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ L0).injective]
    exact S1720H_ne_zero
  have hx_eval : aeval x (S1720H.map (algebraMap ℚ L0)) = 0 :=
    (Polynomial.mem_rootSet_of_ne (p := S1720H.map (algebraMap ℚ L0)) hL0ne).mp hx
  have hprod : aeval x (S1687H.map (algebraMap ℚ L0)) *
      aeval x (S1720SqrtPolynomial.map (algebraMap ℚ L0)) = 0 := by
    change aeval x ((S1687H * S1720SqrtPolynomial).map (algebraMap ℚ L0)) = 0 at hx_eval
    rw [Polynomial.map_mul] at hx_eval
    simpa using hx_eval
  rcases mul_eq_zero.mp hprod with hH | hI
  · -- x is a root of H, hence x^2 is a root of P
    have hH' : aeval x S1687H = 0 := by
      rwa [Polynomial.aeval_map_algebraMap (A := L0) (B := L) x S1687H] at hH
    have hx2' : aeval (x ^ 2) S1687P = 0 := by
      rw [← S1687H_eval_eq (K := L) x]
      exact hH'
    have hx2 : aeval (x ^ 2) (S1687P.map (algebraMap ℚ L0)) = 0 := by
      rwa [Polynomial.aeval_map_algebraMap (A := L0) (B := L) (x ^ 2) S1687P]
    have hisroot : ((S1687P.map (algebraMap ℚ L0)).map (algebraMap L0 L)).IsRoot (x ^ 2) := by
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hx2
    obtain ⟨c0, hc0⟩ := Polynomial.Splits.mem_range_of_isRoot
      (SplittingField.splits S1687P) S1687P_map_ne_zero
      (i := algebraMap L0 L) hisroot
    have hc0root : aeval c0 S1687P = 0 := by
      have h := hx2
      rw [← hc0, Polynomial.aeval_map_algebraMap (A := L0) (B := L)
          (algebraMap L0 L c0) S1687P,
        Polynomial.aeval_algebraMap_apply L c0 S1687P] at h
      exact (algebraMap L0 L).injective (by simpa using h)
    let c : RootP := ⟨c0, (Polynomial.mem_rootSet_of_ne S1687P_ne_zero).mpr hc0root⟩
    have hx2eq : x ^ 2 = (beta c) ^ 2 := by
      rw [beta_sq c]
      exact hc0.symm
    rcases eq_or_eq_neg_of_sq_eq_sq x (beta c) hx2eq with h | h
    · rw [h]
      exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨c, rfl⟩)
    · rw [h]
      exact neg_mem (Algebra.subset_adjoin (Set.mem_union_left _ ⟨c, rfl⟩))
  · -- x is a root of X^2+1, hence x = ± i
    have hI' : aeval x S1720SqrtPolynomial = 0 := by
      rwa [Polynomial.aeval_map_algebraMap (A := L0) (B := L) x S1720SqrtPolynomial] at hI
    have hx2 : x ^ 2 = (-1 : L) := by
      have h := hI'
      unfold S1720SqrtPolynomial at h
      simp only [map_add, map_pow, aeval_X, map_one] at h
      linear_combination h
    have hx2eq : x ^ 2 = iroot ^ 2 := by
      rw [hx2, iroot_sq]
    rcases eq_or_eq_neg_of_sq_eq_sq x iroot hx2eq with h | h
    · rw [h]
      exact Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton iroot))
    · rw [h]
      exact neg_mem (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton iroot)))

theorem adjoin_range_beta_iroot_eq_top :
    Algebra.adjoin L0 (Set.range beta ∪ {iroot}) = ⊤ := by
  apply le_antisymm le_top
  rw [← Polynomial.SplittingField.adjoin_rootSet (f := S1720H.map (algebraMap ℚ L0))]
  exact Algebra.adjoin_le_iff.mpr (fun x hx => root_mem_adjoin x hx)

/-! ## 5. The automorphism group of L over L0 is a 2-group of order at
most 16 -/

theorem beta_sign (σ : L ≃ₐ[L0] L) (c : RootP) :
    σ (beta c) = beta c ∨ σ (beta c) = - beta c := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [← map_pow, beta_sq c, σ.commutes]

theorem i_sign (σ : L ≃ₐ[L0] L) :
    σ iroot = iroot ∨ σ iroot = - iroot := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [← map_pow, iroot_sq, map_neg, map_one]

noncomputable def sgn (σ : L ≃ₐ[L0] L) (c : RootP) : Bool := by
  classical
  exact if σ (beta c) = beta c then true else false

noncomputable def sgnI (σ : L ≃ₐ[L0] L) : Bool := by
  classical
  exact if σ iroot = iroot then true else false

def signFun (σ : L ≃ₐ[L0] L) : (RootP → Bool) × Bool :=
  (sgn σ, sgnI σ)

theorem sgn_eq_true_iff (σ : L ≃ₐ[L0] L) (c : RootP) :
    sgn σ c = true ↔ σ (beta c) = beta c := by
  unfold sgn
  by_cases h : σ (beta c) = beta c <;> simp [h]

theorem sgnI_eq_true_iff (σ : L ≃ₐ[L0] L) :
    sgnI σ = true ↔ σ iroot = iroot := by
  unfold sgnI
  by_cases h : σ iroot = iroot <;> simp [h]

theorem apply_beta_eq_of_sgn_eq (σ τ : L ≃ₐ[L0] L) (c : RootP)
    (h : sgn σ c = sgn τ c) :
    σ (beta c) = τ (beta c) := by
  by_cases hσ : σ (beta c) = beta c
  · have hσb : sgn σ c = true := (sgn_eq_true_iff σ c).mpr hσ
    have hτb : sgn τ c = true := by rw [← h]; exact hσb
    have hτ : τ (beta c) = beta c := (sgn_eq_true_iff τ c).mp hτb
    rw [hσ, hτ]
  · have hτne : ¬ τ (beta c) = beta c := by
      intro hτ
      have hτb : sgn τ c = true := (sgn_eq_true_iff τ c).mpr hτ
      have hσb : sgn σ c = true := by rw [h]; exact hτb
      exact hσ ((sgn_eq_true_iff σ c).mp hσb)
    have hσneg : σ (beta c) = - beta c := (beta_sign σ c).resolve_left hσ
    have hτneg : τ (beta c) = - beta c := (beta_sign τ c).resolve_left hτne
    rw [hσneg, hτneg]

theorem apply_iroot_eq_of_sgnI_eq (σ τ : L ≃ₐ[L0] L)
    (h : sgnI σ = sgnI τ) :
    σ iroot = τ iroot := by
  by_cases hσ : σ iroot = iroot
  · have hσb : sgnI σ = true := (sgnI_eq_true_iff σ).mpr hσ
    have hτb : sgnI τ = true := by rw [← h]; exact hσb
    have hτ : τ iroot = iroot := (sgnI_eq_true_iff τ).mp hτb
    rw [hσ, hτ]
  · have hτne : ¬ τ iroot = iroot := by
      intro hτ
      have hτb : sgnI τ = true := (sgnI_eq_true_iff τ).mpr hτ
      have hσb : sgnI σ = true := by rw [h]; exact hτb
      exact hσ ((sgnI_eq_true_iff σ).mp hσb)
    have hσneg : σ iroot = - iroot := (i_sign σ).resolve_left hσ
    have hτneg : τ iroot = - iroot := (i_sign τ).resolve_left hτne
    rw [hσneg, hτneg]

theorem signFun_injective : Function.Injective signFun := by
  intro σ τ h
  have hgen := adjoin_range_beta_iroot_eq_top
  have hEq : (σ : L →ₐ[L0] L) = (τ : L →ₐ[L0] L) := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨c, rfl⟩
      exact apply_beta_eq_of_sgn_eq σ τ c (congrFun (congrArg Prod.fst h) c)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact apply_iroot_eq_of_sgnI_eq σ τ (congrArg Prod.snd h)
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hEq x)

theorem signFun_card_le : Nat.card (L ≃ₐ[L0] L) ≤ 16 := by
  have hle := Nat.card_le_card_of_injective signFun signFun_injective
  have hcod : Nat.card ((RootP → Bool) × Bool) = 2 ^ Nat.card RootP * 2 := by
    rw [Nat.card_prod, Nat.card_fun]
    simp [Nat.card_eq_fintype_card]
  rw [hcod] at hle
  have hC := RootP_card_le_three
  calc Nat.card (L ≃ₐ[L0] L) ≤ 2 ^ Nat.card RootP * 2 := hle
    _ ≤ 2 ^ 3 * 2 := by
      gcongr
      norm_num
    _ = 16 := by norm_num

theorem aut_sq_one (σ : L ≃ₐ[L0] L) : σ * σ = 1 := by
  have hgen := adjoin_range_beta_iroot_eq_top
  have hEq : ((σ * σ : L ≃ₐ[L0] L) : L →ₐ[L0] L) = ((1 : L ≃ₐ[L0] L) : L →ₐ[L0] L) := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    change (σ * σ) x = (1 : L ≃ₐ[L0] L) x
    rcases hx with hx | hx
    · rcases hx with ⟨c, rfl⟩
      rcases beta_sign σ c with hs | hs
      · rw [AlgEquiv.mul_apply, hs, hs]
        simp
      · rw [AlgEquiv.mul_apply, hs, map_neg, hs]
        simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      rcases i_sign σ with hs | hs
      · rw [AlgEquiv.mul_apply, hs, hs]
        simp
      · rw [AlgEquiv.mul_apply, hs, map_neg, hs]
        simp
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hEq x)

theorem aut_isPGroup : IsPGroup 2 (L ≃ₐ[L0] L) := by
  intro σ
  exact ⟨1, by simpa [pow_two] using aut_sq_one σ⟩

theorem aut_card_dvd_sixteen : Nat.card (L ≃ₐ[L0] L) ∣ 16 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := L ≃ₐ[L0] L)).mp aut_isPGroup
  have hnle : n ≤ 4 := by
    have hle : 2 ^ n ≤ 2 ^ 4 := by
      rw [← hn]
      simpa using signFun_card_le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  rw [hn, show (16 : ℕ) = 2 ^ 4 by norm_num]
  exact pow_dvd_pow 2 hnle

theorem L_finrank_dvd_sixteen : Module.finrank L0 L ∣ 16 := by
  letI : IsSplittingField L0 L (S1720H.map (algebraMap ℚ L0)) :=
    Polynomial.IsSplittingField.splittingField (S1720H.map (algebraMap ℚ L0))
  haveI : FiniteDimensional L0 L :=
    Polynomial.IsSplittingField.finiteDimensional L (S1720H.map (algebraMap ℚ L0))
  haveI : Algebra.IsIntegral L0 L := Algebra.IsIntegral.of_finite L0 L
  haveI : Algebra.IsSeparable L0 L := Algebra.IsSeparable.of_integral L0 L
  haveI : IsGalois L0 L := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hcard : Nat.card (L ≃ₐ[L0] L) = Module.finrank L0 L :=
    IsGalois.card_aut_eq_finrank L0 L
  rw [← hcard]
  exact aut_card_dvd_sixteen

/-! ## 6. The degree of F' -/

theorem L_finrank_dvd_96 : Module.finrank ℚ L ∣ 96 := by
  have h := mul_dvd_mul L0_finrank_dvd_six L_finrank_dvd_sixteen
  rw [Module.finrank_mul_finrank ℚ L0 L] at h
  norm_num at h ⊢
  exact h

noncomputable def S1723Lift : S1720Field →ₐ[ℚ] L :=
  Polynomial.SplittingField.lift (f := S1720H) (L := L) S1720H_splits_L

theorem S1720Field_finrank_dvd_L : Module.finrank ℚ S1720Field ∣ Module.finrank ℚ L := by
  let ψ := S1723Lift
  have hfin : Module.finrank ℚ S1720Field = Module.finrank ℚ ψ.fieldRange :=
    (AlgHom.equivFieldRange ψ).toLinearEquiv.finrank_eq
  rw [hfin]
  have h := IntermediateField.finrank_dvd_of_le_right
    (K := ℚ) (F := ψ.fieldRange) (E := ⊤) le_top
  simpa using h

/-- Main theorem: the degree of the actual paper field over Q divides 96. -/
theorem S1723_finrank_dvd_96 : Module.finrank ℚ S1720Field ∣ 96 :=
  dvd_trans S1720Field_finrank_dvd_L L_finrank_dvd_96

/-- Consequently every prime divisor of [F' : Q] is at most 3. -/
theorem S1723_finrank_prime_factors_le_three :
    ∀ p : ℕ, p.Prime → p ∣ Module.finrank ℚ S1720Field → p ≤ 3 := by
  intro p hp hpdvd
  have h96 : p ∣ 96 := hpdvd.trans S1723_finrank_dvd_96
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

/-- The exact degreePrimeToL input for F', now unconditional. -/
theorem S1723DegreePrimeToL (l : PrimeGeFive) : S1720DegreePrimeToL l := by
  unfold S1720DegreePrimeToL
  exact (coprime_96_primeGeFive l).coprime_dvd_left S1723_finrank_dvd_96

/-- Unconditional actual arithmetic data for the S1667 curve. -/
noncomputable def S1723InitialThetaArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l :=
  S1720InitialThetaArithmeticData l (S1723DegreePrimeToL l)

#print axioms S1723_finrank_dvd_96
#print axioms S1723DegreePrimeToL

end LeanFormal.IUT.XiFPaper.S1723DegreeBoundActual
