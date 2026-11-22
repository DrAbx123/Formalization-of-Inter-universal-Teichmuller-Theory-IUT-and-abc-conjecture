
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace

namespace S2223Probe

universe u

variable {F : Type u} [Field F] [NumberField F]

abbrev L (place : NumberField.FinitePlace F) : Type u := Completion place
abbrev Lbar (place : NumberField.FinitePlace F) : Type u := AlgebraicClosure (Completion place)

noncomputable def qU (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) : (Lbar place)ˣ :=
  tateParameterUnit place parameter.q parameter.q_ne_zero

abbrev Deck (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) : Type u :=
  (Lbar place)ˣ ⧸ Subgroup.zpowers (qU place parameter)

theorem qUnit_zpow_eq_one_iff (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) (m : ℤ) :
    qU place parameter ^ m = 1 ↔ m = 0 := by
  constructor
  · intro hm
    have hm' : (((qU place parameter) ^ m : (Lbar place)ˣ) : Lbar place) = 1 := by
      rw [hm]; rfl
    have hval : algebraMap (L place) (Lbar place) (parameter.q ^ m) = 1 := by
      simpa [qU, NumberFieldFinitePlace.tateParameterUnit, Units.val_pow_eq_pow_val] using hm'
    have hq : parameter.q ^ m = 1 := by
      apply (algebraMap (L place) (Lbar place)).injective
      simpa using hval
    have hnorm : ‖parameter.q‖ ^ m = 1 := by
      calc ‖parameter.q‖ ^ m = ‖parameter.q ^ m‖ := (norm_zpow _ _).symm
        _ = ‖(1 : L place)‖ := by rw [hq]
        _ = 1 := by simp
    have hpos : 0 < ‖parameter.q‖ := norm_pos_iff.mpr parameter.q_ne_zero
    have hne : ‖parameter.q‖ ≠ 1 := by
      intro h
      have hlt : ‖parameter.q‖ < 1 := by
        rw [Valued.toNormedField.norm_lt_one_iff]
        exact parameter.valuation_lt_one
      rw [h] at hlt
      exact lt_irrefl 1 hlt
    exact (zpow_eq_one_iff_right₀ hpos.le hne).mp hnorm
  · intro hm
    rw [hm, zpow_zero]

theorem exists_rep_of_fixed_torsion
    (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place)
    {X : PuncturedEllipticCurve F}
    (comparison : TatePointComparison X place parameter)
    (n : Nat) (hn : 0 < n)
    (P : (X.baseChange (L place)).AlgebraicClosurePoint)
    (hPn : n • P = 0)
    (hPfix : ∀ σ : (Lbar place) ≃ₐ[L place] (Lbar place),
      (X.baseChange (L place)).galoisActionOnPoint σ P = P) :
    ∃ (x : (L place)ˣ) (m : ℤ),
      comparison.pointEquiv (QuotientGroup.mk
        (Units.map (algebraMap (L place) (Lbar place)).toMonoidHom x) : Deck place parameter)
        = Multiplicative.ofAdd P ∧
      (x : L place) ^ (n : ℤ) = parameter.q ^ m := by
  classical
  let z : Deck place parameter := comparison.pointEquiv.symm (Multiplicative.ofAdd P)
  have hzP : comparison.pointEquiv z = Multiplicative.ofAdd P :=
    MulEquiv.apply_symm_apply comparison.pointEquiv _
  have hzpow : z ^ n = 1 := by
    apply comparison.pointEquiv.injective
    rw [map_pow, hzP, ofAdd_nsmul, hPn, ofAdd_zero, map_one]
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective z
  have hzfix (σ : (Lbar place) ≃ₐ[L place] (Lbar place)) :
      (QuotientGroup.mk (Units.map σ.toRingEquiv.toMonoidHom x) : Deck place parameter) = z := by
    apply comparison.pointEquiv.injective
    rw [comparison.galois_naturality σ x, hx, hzP, hPfix σ]
    exact hzP.symm
  have hdiv (σ : (Lbar place) ≃ₐ[L place] (Lbar place)) :
      Units.map σ.toRingEquiv.toMonoidHom x / x ∈ Subgroup.zpowers (qU place parameter) := by
    exact QuotientGroup.eq_iff_div_mem.mp (hzfix σ)
  have hxpow_mem : x ^ n ∈ Subgroup.zpowers (qU place parameter) := by
    have h : (QuotientGroup.mk (x ^ n) : Deck place parameter) = 1 := by
      rw [← map_pow, hx, hzpow]
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxpow_mem
  have hfix_x : ∀ σ : (Lbar place) ≃ₐ[L place] (Lbar place), σ ((x : Lbar place)) = (x : Lbar place) := by
    intro σ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hdiv σ)
    have hqfix : Units.map σ.toRingEquiv.toMonoidHom (qU place parameter) = qU place parameter :=
      NumberFieldFinitePlace.tateParameterUnit_algEquiv_map place parameter.q parameter.q_ne_zero σ
    have hσxpow : (Units.map σ.toRingEquiv.toMonoidHom x) ^ n = x ^ n := by
      calc (Units.map σ.toRingEquiv.toMonoidHom x) ^ n
          = Units.map σ.toRingEquiv.toMonoidHom (x ^ n) := by rw [map_pow]
        _ = Units.map σ.toRingEquiv.toMonoidHom ((qU place parameter) ^ m) := by rw [hm]
        _ = (Units.map σ.toRingEquiv.toMonoidHom (qU place parameter)) ^ m := by rw [map_pow]
        _ = (qU place parameter) ^ m := by rw [hqfix]
        _ = x ^ n := hm
    have hu_pow : (Units.map σ.toRingEquiv.toMonoidHom x / x) ^ n = 1 := by
      rw [div_pow, hσxpow, div_self (pow_ne_zero n (Units.ne_zero x))]
    have hk_pow : (qU place parameter) ^ (k * (n : ℤ)) = 1 := by
      rw [zpow_mul, hk, hu_pow]
    have hk0 : k * (n : ℤ) = 0 :=
      (qUnit_zpow_eq_one_iff place parameter (k * (n : ℤ))).mp hk_pow
    have hkzero : k = 0 := by
      have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      exact (mul_eq_zero.mp hk0).resolve_right hn'
    have hunit : Units.map σ.toRingEquiv.toMonoidHom x / x = 1 := by
      rw [hkzero, zpow_zero] at hk
      exact hk.symm
    have hval := congrArg (fun u : (Lbar place)ˣ => (u : Lbar place)) hunit
    simpa using hval
  have hxL : ∃ xL : L place, algebraMap (L place) (Lbar place) xL = (x : Lbar place) := by
    have hmem : (x : Lbar place) ∈ (⊥ : IntermediateField (L place) (Lbar place)) := by
      rw [InfiniteGalois.mem_bot_iff_fixed]
      exact hfix_x
    exact IntermediateField.mem_bot.mp hmem
  obtain ⟨xL, hxL⟩ := hxL
  have hxL_ne : xL ≠ 0 := by
    intro h0
    have : (x : Lbar place) = 0 := by rw [← hxL, h0, map_zero]
    exact Units.ne_zero x this
  refine ⟨Units.mk0 xL hxL_ne, m, ?_, ?_⟩
  · have hxunit : Units.map (algebraMap (L place) (Lbar place)).toMonoidHom (Units.mk0 xL hxL_ne) = x := by
      ext
      simp [hxL]
    rw [hxunit]
    exact hx
  · have h := congrArg (fun u : (Lbar place)ˣ => (u : Lbar place)) hm
    have h' : algebraMap (L place) (Lbar place) ((Units.mk0 xL hxL_ne : (L place)ˣ) ^ (n : ℤ)) =
        algebraMap (L place) (Lbar place) (parameter.q ^ m) := by
      simp only [Units.val_zpow_eq_zpow_val]
      rw [← h]
      simp [qU, NumberFieldFinitePlace.tateParameterUnit, hxL]
    exact (algebraMap (L place) (Lbar place)).injective h'

end S2223Probe
end
