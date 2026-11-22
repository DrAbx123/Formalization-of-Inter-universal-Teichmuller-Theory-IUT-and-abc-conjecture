import tmp.sheaf.xif.paper.S1448ReportENormalizedNormActual
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.Ideal.Int

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# S1492: actual scalar-extension compatibility for the normalized norm

For a finite place `place` of a number field `F`, this file proves

  `ScalarExtensionCompatibility place`,

i.e. for every `q : PadicScalarField place = ℚ_[p]`,

  `canonicalAbsValue place (algebraMap (K place) (N place) q) = ‖q‖`.

The proof is the actual p-adic DVR computation:

* every nonzero `q` is `p^m * u` with `u` a p-adic integral unit;
* `toAdd_valuation_completionMap` (equivalently `valuation_completionMap`)
  gives the upper valuation of the completion image;
* `completionIntegersMap` is applied to the completed valuation rings of the
  unit part (its unit preservation, with the local-hom statement available);
* the residue-norm base identity `absNorm = p^f` and `d = e * f` turn
  `absNorm ^ (-(ν/d))` into the p-adic norm `p ^ (-m)`.

No hypothesis, no sorry, and no change of the target statement.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1492ScalarExtensionCompatibilityActual

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1448ReportENormalizedNormActual

universe u

variable {F : Type u} [Field F] [NumberField F] (place : NumberField.FinitePlace F)

abbrev K (place : NumberField.FinitePlace F) : Type := PadicScalarField place
abbrev N (place : NumberField.FinitePlace F) : Type u := NormalizedCompletion place
abbrev L (place : NumberField.FinitePlace F) : Type :=
  (comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ
abbrev R : Type := NumberField.RingOfIntegers ℚ
abbrev vQ (place : NumberField.FinitePlace F) : IsDedekindDomain.HeightOneSpectrum R :=
  (comap (k := ℚ) place).maximalIdeal

local instance adicAlgebra : Algebra ℚ (L place) :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (NumberField.RingOfIntegers ℚ) ℚ
    (comap (k := ℚ) place).maximalIdeal

local instance factPrimeEquiv :
    Fact (Nat.Prime ↑(Rat.HeightOneSpectrum.primesEquiv (vQ place))) :=
  completionRationalPrime_fact place

local instance valuedN : Valued (N place) (WithZero (Multiplicative ℤ)) := by
  change Valued (place.maximalIdeal.adicCompletion F) (WithZero (Multiplicative ℤ))
  infer_instance

abbrev pNat (place : NumberField.FinitePlace F) : ℕ :=
  S1448ReportENormalizedNormActual.pNat place
abbrev e (place : NumberField.FinitePlace F) : ℕ :=
  S1448ReportENormalizedNormActual.e place
abbrev f (place : NumberField.FinitePlace F) : ℕ :=
  S1448ReportENormalizedNormActual.f place
abbrev d (place : NumberField.FinitePlace F) : ℕ :=
  S1448ReportENormalizedNormActual.d place
abbrev absNorm (place : NumberField.FinitePlace F) : ℝ :=
  S1448ReportENormalizedNormActual.absNorm place

/-! ## The residue-norm base is the rational prime -/

theorem absNorm_lower_eq_pNat :
    Ideal.absNorm (comap (k := ℚ) place).maximalIdeal.asIdeal = pNat place := by
  let J := (comap (k := ℚ) place).maximalIdeal.asIdeal
  let f0 := Rat.IsIntegralClosure.intEquiv R
  have hmap : J.map f0 = Ideal.span {(pNat place : ℤ)} := by
    rw [← Rat.HeightOneSpectrum.span_natGenerator (comap (k := ℚ) place).maximalIdeal]
    congr 1
  have hcard : Ideal.absNorm J = Ideal.absNorm (J.map f0) := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv J (J.map f0) f0 rfl).toEquiv
  rw [hcard, hmap, Ideal.absNorm_apply, Submodule.cardQuot_apply, Int.card_ideal_quot]

theorem absNorm_eq_prime_pow :
    absNorm place = (pNat place : ℝ) ^ f place := by
  change (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) = (pNat place : ℝ) ^ f place
  rw [LeanFormal.IUT.NumberFieldFinitePlace.absNorm_eq_pow_relativeResidueDegree
    (k := ℚ) place]
  rw [absNorm_lower_eq_pNat place]

/-! ## The rational prime valuation in the lower completion -/

theorem lowerPrimeGlobal :
    (vQ place).valuation ℚ (pNat place : ℚ) = WithZero.exp (-1 : ℤ) := by
  let f0 := Rat.IsIntegralClosure.intEquiv R
  let r : R := f0.symm (pNat place : ℤ)
  have hf : f0 = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hr_coe : (r : ℚ) = (pNat place : ℚ) := by
    have hr : r = Rat.ringOfIntegersEquiv.symm (pNat place : ℤ) := by
      simp only [r, hf]
    rw [hr, Rat.ringOfIntegersEquiv_symm_apply_coe]
    norm_num
  have hv : (vQ place).asIdeal = Ideal.span {r} := by
    have hmap : (vQ place).asIdeal.map f0 = Ideal.span {(pNat place : ℤ)} := by
      rw [← Rat.HeightOneSpectrum.span_natGenerator (vQ place)]
      congr 1
    have hinv : Ideal.map (f0.symm : ℤ →+* R)
          (Ideal.map (f0 : R →+* ℤ) (vQ place).asIdeal) =
        Ideal.map (f0.symm : ℤ →+* R) (Ideal.span {(pNat place : ℤ)}) :=
      congrArg (Ideal.map (f0.symm : ℤ →+* R)) hmap
    have hleft : Ideal.map (f0.symm : ℤ →+* R)
          (Ideal.map (f0 : R →+* ℤ) (vQ place).asIdeal) = (vQ place).asIdeal := by
      rw [Ideal.map_map (f := (f0 : R →+* ℤ)) (g := (f0.symm : ℤ →+* R)),
        RingEquiv.symm_comp, Ideal.map_id]
    have hright : Ideal.map (f0.symm : ℤ →+* R) (Ideal.span {(pNat place : ℤ)}) =
        Ideal.span {r} := by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {f0.symm (pNat place : ℤ)} = Ideal.span {r}
      rfl
    rw [hleft, hright] at hinv
    exact hinv
  have hr0 : r ≠ 0 := by
    intro h
    have : (pNat place : ℤ) = 0 := by
      rw [← show f0 r = (pNat place : ℤ) from f0.apply_symm_apply _]
      rw [h, map_zero]
    exact (Nat.Prime.ne_zero (completionRationalPrime place).2) (by exact_mod_cast this)
  rw [show (pNat place : ℚ) = (r : ℚ) from hr_coe.symm]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton (vQ place) hr0 hv

theorem lowerPrimeValuation :
    Valued.v (algebraMap ℚ (L place) (pNat place : ℚ)) = WithZero.exp (-1 : ℤ) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply]
  change Valued.v ({ toCompletion :=
      ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation ℚ (vQ place))).symm
        (pNat place : ℚ)) } : L place) = WithZero.exp (-1 : ℤ)
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact lowerPrimeGlobal place

/-! ## The rational prime in the p-adic scalar field -/

theorem nonzero_algebraMap_pNat :
    algebraMap ℚ (K place) (pNat place : ℚ) ≠ 0 := by
  intro h
  have hq : (pNat place : ℚ) = 0 :=
    (algebraMap ℚ (K place)).injective (by simpa using h)
  have hp : (pNat place : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero (show Nat.Prime (pNat place) from
      (completionRationalPrime place).2))
  exact hp (by exact_mod_cast hq)

theorem scalarPrime_norm :
    ‖algebraMap ℚ (K place) (pNat place : ℚ)‖ = (pNat place : ℝ)⁻¹ := by
  rw [Padic.norm_eq_zpow_neg_valuation (nonzero_algebraMap_pNat place)]
  rw [show (algebraMap ℚ (K place) (pNat place : ℚ)).valuation = 1 from by
    simpa using (Padic.valuation_p (p := pNat place))]
  norm_num

theorem ratPreimage :
    (rationalCompletionPadicEquiv place).symm (algebraMap ℚ (K place) (pNat place : ℚ)) =
      algebraMap ℚ (L place) (pNat place : ℚ) := by
  rw [← (rationalCompletionPadicEquiv place).commutes (pNat place : ℚ)]
  exact (rationalCompletionPadicEquiv place).symm_apply_apply _

theorem algebraMap_padicPrime_eq_completionMap :
    algebraMap (K place) (N place) (algebraMap ℚ (K place) (pNat place : ℚ)) =
      completionMap place (algebraMap ℚ (L place) (pNat place : ℚ)) := by
  change completionMap place
      ((rationalCompletionPadicEquiv place).symm (algebraMap ℚ (K place) (pNat place : ℚ))) =
    completionMap place (algebraMap ℚ (L place) (pNat place : ℚ))
  rw [ratPreimage place]

/-! ## The upper prime valuation -/

theorem upperPrimeValuation :
    Valued.v (completionMap place (algebraMap ℚ (L place) (pNat place : ℚ))) =
      WithZero.exp (-(e place : ℤ)) := by
  have hx : algebraMap ℚ (L place) (pNat place : ℚ) ≠ 0 := by
    intro h
    have hval := lowerPrimeValuation place
    rw [h, map_zero] at hval
    exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) hval.symm
  have hmap : completionMap place (algebraMap ℚ (L place) (pNat place : ℚ)) ≠ 0 := by
    intro h
    apply hx
    apply completionMap_injective place
    simpa using h
  have hadd := toAdd_valuation_completionMap (k := ℚ) (K := F) place
    (algebraMap ℚ (L place) (pNat place : ℚ)) hx hmap
  have hlow : Multiplicative.toAdd (WithZero.unzero
      (valuation_ne_zero_of_ne_zero (comap (k := ℚ) place)
        (algebraMap ℚ (L place) (pNat place : ℚ)) hx)) = -1 := by
    rw [WithZero.toAdd_unzero_eq_iff _ (-1)]
    rw [lowerPrimeValuation place]
    rfl
  rw [hlow] at hadd
  have htarget : Multiplicative.toAdd (WithZero.unzero
      (valuation_ne_zero_of_ne_zero place
        (completionMap place (algebraMap ℚ (L place) (pNat place : ℚ))) hmap)) = -(e place : ℤ) := by
    rw [hadd]
    rw [show e place = relativeRamificationIndex (k := ℚ) place from rfl]
    ring
  have hv : Valued.v (completionMap place (algebraMap ℚ (L place) (pNat place : ℚ))) ≠ 0 :=
    valuation_ne_zero_of_ne_zero place
      (completionMap place (algebraMap ℚ (L place) (pNat place : ℚ))) hmap
  exact (WithZero.toAdd_unzero_eq_iff hv (-(e place : ℤ))).mp htarget

/-! ## The p-adic unit part -/

theorem padicUnit_norm_one (u : ℤ_[pNat place]ˣ) :
    ‖((u : ℤ_[pNat place]) : K place)‖ = 1 := by
  rw [PadicInt.padic_norm_e_of_padicInt]
  exact PadicInt.norm_units u

theorem unitValuation (u : K place) (hu : u ≠ 0) (hunorm : ‖u‖ = 1) :
    Valued.v (algebraMap (K place) (N place) u) = 1 := by
  let u_int : ℤ_[pNat place]ˣ := PadicInt.mkUnits hunorm
  have hu_int : ((u_int : ℤ_[pNat place]) : K place) = u := PadicInt.mkUnits_eq hunorm
  have hbij := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn (v := vQ place)
  have hu_mem : ((u_int : ℤ_[pNat place]) : K place) ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv (vQ place)) := by
    change ‖((u_int : ℤ_[pNat place]) : K place)‖ ≤ 1
    rw [padicUnit_norm_one place u_int]
  obtain ⟨x, hx_mem, hx_eq⟩ := hbij.2.2 hu_mem
  have hu_inv_mem : (((u_int : ℤ_[pNat place]) : K place))⁻¹ ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv (vQ place)) := by
    change ‖(((u_int : ℤ_[pNat place]) : K place))⁻¹‖ ≤ 1
    rw [norm_inv, padicUnit_norm_one place u_int]
    norm_num
  obtain ⟨y, hy_mem, hy_eq⟩ := hbij.2.2 hu_inv_mem
  have hu_ne : ((u_int : ℤ_[pNat place]) : K place) ≠ 0 := by
    intro h
    have := congrArg norm h
    rw [padicUnit_norm_one place u_int, norm_zero] at this
    norm_num at this
  have hx_ne : x ≠ 0 := by
    intro hx0
    apply hu_ne
    rw [← hx_eq, hx0, map_zero]
    rfl
  have hx_val : Valued.v x = 1 := by
    have hx_le : Valued.v x ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (R := R) (K := ℚ) (v := vQ place)).mp hx_mem
    have hy_le : Valued.v x⁻¹ ≤ 1 := by
      have hy_eq_inv : y = x⁻¹ := by
        apply (rationalCompletionPadicEquiv place).injective
        change (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vQ place)) y =
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vQ place)) x⁻¹
        rw [hy_eq, map_inv₀, hx_eq]
        rfl
      rw [← hy_eq_inv]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (R := R) (K := ℚ) (v := vQ place)).mp hy_mem
    have hx_pos : 0 < Valued.v x :=
      WithZero.pos_iff_ne_zero.mpr
        (valuation_ne_zero_of_ne_zero (comap (k := ℚ) place) x hx_ne)
    have hx_ge : 1 ≤ Valued.v x := (inv_le_one₀ hx_pos).mp (by simpa using hy_le)
    exact le_antisymm hx_le hx_ge
  have hx_unit : IsUnit (⟨x, hx_mem⟩ : (vQ place).adicCompletionIntegers ℚ) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hx_val
  have hupper_unit : IsUnit (completionIntegersMap place ⟨x, hx_mem⟩) :=
    hx_unit.map (completionIntegersMap place)
  have hupper_val : Valued.v
      ((completionIntegersMap place ⟨x, hx_mem⟩ :
        place.maximalIdeal.adicCompletionIntegers F) :
        place.maximalIdeal.adicCompletion F) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp
      hupper_unit
  have hmap_val : Valued.v (completionMap place x) = 1 := by
    simpa [coe_completionIntegersMap] using hupper_val
  have hupper : algebraMap (K place) (N place) u = completionMap place x := by
    change completionMap place ((rationalCompletionPadicEquiv place).symm u) = completionMap place x
    congr 1
    rw [← hu_int]
    exact (rationalCompletionPadicEquiv place).symm_apply_eq.mpr hx_eq.symm
  rw [hupper]
  exact hmap_val

/-! ## The base scalar valuation relation -/

theorem baseScalarValuation (q : K place) (hq : q ≠ 0) :
    ∃ m : ℤ, q = (algebraMap ℚ (K place) (pNat place : ℚ)) ^ m *
        (q * (algebraMap ℚ (K place) (pNat place : ℚ)) ^ (-m)) ∧
      Valued.v (algebraMap (K place) (N place) q) = WithZero.exp (-(m * (e place : ℤ))) ∧
      ‖q‖ = (pNat place : ℝ) ^ (-m : ℤ) := by
  let pK : K place := algebraMap ℚ (K place) (pNat place : ℚ)
  let m : ℤ := q.valuation
  let u : K place := q * pK ^ (-m)
  have hpK_ne : pK ≠ 0 := nonzero_algebraMap_pNat place
  have hqnorm : ‖q‖ = (pNat place : ℝ) ^ (-m : ℤ) := by
    rw [Padic.norm_eq_zpow_neg_valuation hq]
  have hu_norm : ‖u‖ = 1 := by
    show ‖q * pK ^ (-m)‖ = 1
    rw [norm_mul, norm_zpow, hqnorm]
    rw [show ‖pK‖ = (pNat place : ℝ)⁻¹ from scalarPrime_norm place]
    rw [show ((pNat place : ℝ)⁻¹) ^ (-m) = (pNat place : ℝ) ^ m from by
      rw [inv_zpow, ← zpow_neg, neg_neg]]
    rw [← zpow_add₀ (by exact_mod_cast (Nat.Prime.ne_zero (show Nat.Prime (pNat place) from
      (completionRationalPrime place).2)))]
    simp
  have hu_ne : u ≠ 0 := by
    show q * pK ^ (-m) ≠ 0
    exact mul_ne_zero hq (zpow_ne_zero _ hpK_ne)
  have hval_u : Valued.v (algebraMap (K place) (N place) u) = 1 :=
    unitValuation place u hu_ne hu_norm
  have hval_p : Valued.v (algebraMap (K place) (N place) pK) =
      WithZero.exp (-(e place : ℤ)) := by
    rw [show algebraMap (K place) (N place) pK =
      completionMap place (algebraMap ℚ (L place) (pNat place : ℚ)) from
        algebraMap_padicPrime_eq_completionMap place]
    exact upperPrimeValuation place
  have hdecomp : q = pK ^ m * u := by
    show q = pK ^ m * (q * pK ^ (-m))
    calc q = q * 1 := (mul_one q).symm
      _ = q * (pK ^ m * pK ^ (-m)) := by rw [← zpow_add₀ hpK_ne]; simp
      _ = pK ^ m * (q * pK ^ (-m)) := by ring
  have hval_q : Valued.v (algebraMap (K place) (N place) q) =
      WithZero.exp (-(m * (e place : ℤ))) := by
    rw [hdecomp, map_mul (algebraMap (K place) (N place)),
      map_zpow₀ (algebraMap (K place) (N place))]
    rw [show Valued.v ((algebraMap (K place) (N place)) pK ^ m *
          (algebraMap (K place) (N place)) u) =
        Valued.v ((algebraMap (K place) (N place)) pK ^ m) *
          Valued.v ((algebraMap (K place) (N place)) u) from (Valued.v).map_mul' _ _]
    rw [show Valued.v ((algebraMap (K place) (N place)) pK ^ m) =
        (Valued.v ((algebraMap (K place) (N place)) pK)) ^ m from
      map_zpow₀ (Valued.v).toMonoidWithZeroHom _ m]
    rw [hval_u, hval_p, mul_one]
    rw [← WithZero.exp_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_neg]
    simp
  exact ⟨m, hdecomp, hval_q, hqnorm⟩

/-! ## The exact scalar-extension compatibility -/

theorem rpow_prime_pow_div (m : ℤ) :
    absNorm place ^ (-((m * e place : ℤ) : ℝ) / (d place : ℝ)) =
      (pNat place : ℝ) ^ (-m : ℤ) := by
  have hP : (0 : ℝ) < (pNat place : ℝ) := by
    exact_mod_cast (completionRationalPrime place).2.pos
  have hE : (e place : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (relativeRamificationIndex_ne_zero (k := ℚ) place)).ne'
  have hF : (f place : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (relativeResidueDegree_ne_zero (k := ℚ) place)).ne'
  rw [show absNorm place = (pNat place : ℝ) ^ f place from absNorm_eq_prime_pow place]
  rw [show d place = e place * f place from rfl]
  rw [← Real.rpow_natCast (pNat place : ℝ) (f place)]
  rw [← Real.rpow_mul (le_of_lt hP)]
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  field_simp [hE, hF]

theorem scalarExtensionCompatibility :
    ScalarExtensionCompatibility place := by
  intro q
  by_cases hq : q = 0
  · subst hq
    simp [canonicalAbsValue]
  · obtain ⟨m, hdecomp, hval, hqnorm⟩ := baseScalarValuation place q hq
    have hxq : algebraMap (K place) (N place) q ≠ 0 := by
      intro h
      have hx : (rationalCompletionPadicEquiv place).symm q = 0 := by
        apply completionMap_injective place
        change completionMap place ((rationalCompletionPadicEquiv place).symm q) = 0 at h
        simpa using h
      have hq0 : q = 0 := by
        have := congrArg (rationalCompletionPadicEquiv place) hx
        simpa using this
      exact hq hq0
    have hnu : nu place (algebraMap (K place) (N place) q) = m * (e place : ℤ) := by
      unfold nu
      rw [hval, WithZero.log_exp]
      ring
    rw [canonicalAbsValue_of_ne place hxq, hnu, hqnorm]
    exact rpow_prime_pow_div place m

end LeanFormal.IUT.XiFPaper.S1492ScalarExtensionCompatibilityActual