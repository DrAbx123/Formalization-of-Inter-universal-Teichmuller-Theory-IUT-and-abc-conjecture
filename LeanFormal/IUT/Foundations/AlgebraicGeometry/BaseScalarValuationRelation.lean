import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual
import Mathlib.NumberTheory.Padics.PadicIntegers
import LeanFormal.IUT.Foundations.AlgebraicGeometry.PadicScalarValuationConstruction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Base-scalar valuation relation from p-adic DVR decomposition

For `q : ℚ_[p]` decomposed as `q = p^m * u` with `u` a `p`-adic integral unit,
this file proves

  `Valued.v (algebraMap q : completion) = exp(-e*m)`,

where `e` is the relative ramification index of the place.  The proof combines
multiplicativity, the prime-power valuation, and the unit valuation one.

No fake base-scalar valuation.
-/

noncomputable section

namespace LeanFormal.IUT.BaseScalarValuationRelation

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PadicScalarValuationConstruction

universe u

variable {F : Type u} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

abbrev scalarField : Type := PadicScalarField place
abbrev completionField : Type u := place.maximalIdeal.adicCompletion F
abbrev pNat : ℕ := (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val
abbrev ramification : ℕ := relativeRamificationIndex (k := ℚ) place

local instance factPrime : Fact (pNat place).Prime :=
  ⟨(LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2⟩

/-- The `ℚ`-algebra structure on the upper completion used below is Mathlib's
adic-completion algebra structure (and not the generic division-ring rational
algebra), so that it is the structure used by `completionMap` and by the
ramification formula. -/
local instance upperCompletionAlgebraRat : Algebra ℚ (completionField place) :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (K := F) (S := ℚ) (v := place.maximalIdeal)

/-- The `ℚ`-algebra structure on the lower (rational) completion, again the
adic-completion structure used by the ramification formula. -/
local instance lowerCompletionAlgebraRat :
    Algebra ℚ ((comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ) :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (K := ℚ) (S := ℚ) (v := (comap (k := ℚ) place).maximalIdeal)

/-- The actual `ℚ_[p]`-algebra structure on the completion field, induced by the
actual completion embedding `padicCompletionHom`. -/
noncomputable abbrev scalarAlgebra :
    Algebra (scalarField place) (completionField place) :=
  (LeanFormal.IUT.NumberFieldFinitePlace.padicCompletionHom place).toAlgebra

local instance scalarAlgebraInstance : Algebra (scalarField place) (completionField place) :=
  scalarAlgebra place

theorem scalarAlgebra_algebraMap :
    (algebraMap (scalarField place) (completionField place)) =
      LeanFormal.IUT.NumberFieldFinitePlace.padicCompletionHom place :=
  rfl

/-- The canonical rational cast of the algebra structure coincides with `Rat.cast`. -/
theorem algebraMap_ratCast_eq' {A : Type*} [DivisionRing A] [Algebra ℚ A] (q : ℚ) :
    algebraMap ℚ A q = (q : A) := by
  have h := map_ratCast (algebraMap ℚ A) q
  rwa [Rat.cast_id] at h

/-- The value-group identity `exp (-1)^n = exp (-n)` used for prime powers. -/
theorem withZero_exp_neg_one_pow (n : ℕ) :
    WithZero.exp (-1 : ℤ) ^ n = WithZero.exp (-(n : ℤ)) := by
  rw [← WithZero.exp_nsmul]
  congr 1
  simp

/-! ## The rational prime valuation -/

theorem lowerPrimeValuation :
    (Valued.v (((pNat place : ℚ) : LeanFormal.IUT.NumberFieldFinitePlace.Completion
      (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) place)))) =
      WithZero.exp (-1 : ℤ) := by
  -- the lower place is the rational `p`-adic place; the integer `p` generates the
  -- corresponding height-one prime, hence has valuation `exp (-1)`
  let v := (comap (k := ℚ) place).maximalIdeal
  let e := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  let r : NumberField.RingOfIntegers ℚ := e.symm (pNat place : ℤ)
  have hprime : (pNat place).Prime :=
    (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2
  have he : e = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hr : r = Rat.ringOfIntegersEquiv.symm (pNat place : ℤ) := by
    simp only [r, he]
  have hr_coe : ((r : ℚ)) = (pNat place : ℚ) := by
    rw [hr]
    exact Rat.ringOfIntegersEquiv_symm_apply_coe (pNat place : ℤ)
  have hr_ne : r ≠ 0 := by
    intro h
    have h0 : (pNat place : ℤ) = 0 := by
      simpa [r] using congrArg e h
    exact hprime.ne_zero (by exact_mod_cast h0)
  have hv : v.asIdeal = Ideal.span {r} := by
    have hspan : Ideal.span {(pNat place : ℤ)} = v.asIdeal.map e := by
      have h := Rat.HeightOneSpectrum.span_natGenerator v
      rwa [show Rat.HeightOneSpectrum.natGenerator v = pNat place from rfl] at h
    have her : e r = (pNat place : ℤ) := by
      simpa [r] using e.apply_symm_apply (pNat place : ℤ)
    refine SetLike.ext ?_
    intro x
    constructor
    · intro hx
      have hex : e x ∈ Ideal.span {(pNat place : ℤ)} := by
        rw [hspan]
        exact Ideal.mem_map_of_mem e hx
      rw [Ideal.mem_span_singleton] at hex
      rw [Ideal.mem_span_singleton]
      obtain ⟨c, hc⟩ := hex
      refine ⟨e.symm c, ?_⟩
      apply e.injective
      rw [map_mul, her, e.apply_symm_apply]
      exact hc
    · intro hx
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      have hex : e x ∈ Ideal.span {(pNat place : ℤ)} := by
        rw [Ideal.mem_span_singleton]
        refine ⟨e c, ?_⟩
        rw [hc, map_mul, her]
      rw [hspan, Ideal.mem_map_iff_of_surjective (f := e) e.surjective] at hex
      obtain ⟨y, hy, hxy⟩ := hex
      have hyx : y = x := e.injective hxy
      rwa [hyx] at hy
  have hval : v.intValuation r = WithZero.exp (-1 : ℤ) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton v hr_ne hv
  have hmain : v.valuation ℚ ((r : ℚ)) = WithZero.exp (-1 : ℤ) :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) (v := v) r).trans hval
  have hgoal :
      ((pNat place : ℚ) : LeanFormal.IUT.NumberFieldFinitePlace.Completion
        (comap (k := ℚ) place)) =
        ((r : ℚ) : (comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ) := by
    rw [← hr_coe]
  rw [hgoal]
  rw [← algebraMap_ratCast_eq' (A := (comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ) (r : ℚ)]
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (K := ℚ) (v := v) (k := (r : ℚ))).trans hmain

theorem upperPrimeValuation :
    (Valued.v (algebraMap ℚ (completionField place) ((pNat place : ℚ))) :
      WithZero (Multiplicative ℤ)) = WithZero.exp (-(ramification place : ℤ)) := by
  have h := LeanFormal.IUT.NumberFieldFinitePlace.valuation_algebraMap
    (k := ℚ) (K := F) place (pNat place : ℚ)
  have hlow' : Valued.v (algebraMap ℚ ((comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ)
      (pNat place : ℚ)) = WithZero.exp (-1 : ℤ) := by
    rw [algebraMap_ratCast_eq' (A := (comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ)
      (pNat place : ℚ)]
    exact lowerPrimeValuation place
  have hlow : (comap (k := ℚ) place).maximalIdeal.valuation ℚ ((pNat place : ℚ)) =
      WithZero.exp (-1 : ℤ) :=
    (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (K := ℚ) (v := (comap (k := ℚ) place).maximalIdeal)
      (k := (pNat place : ℚ))).symm.trans hlow'
  have hup : Valued.v (algebraMap ℚ (completionField place) (pNat place : ℚ)) =
      place.maximalIdeal.valuation F (algebraMap ℚ F (pNat place : ℚ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
      (K := F) (S := ℚ) (v := place.maximalIdeal)]
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (K := F) (v := place.maximalIdeal) (k := algebraMap ℚ F (pNat place : ℚ))
  have h' := h
  rw [show (comap (k := ℚ) place).maximalIdeal.valuation ℚ ((pNat place : ℚ)) =
      WithZero.exp (-1 : ℤ) from hlow, withZero_exp_neg_one_pow] at h'
  rw [hup]
  exact h'.symm

/-! ## p-adic DVR decomposition -/

theorem scalarPrime_norm :
    ‖((pNat place : ℚ) : scalarField place)‖ = (pNat place : ℝ)⁻¹ := by
  have hprime : (pNat place).Prime :=
    (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2
  have hne : ((pNat place : ℚ) : scalarField place) ≠ 0 := by
    exact_mod_cast hprime.ne_zero
  rw [Padic.norm_eq_zpow_neg_valuation (p := pNat place) hne]
  have hval : (((pNat place : ℚ) : scalarField place)).valuation = 1 := by
    have hcast : ((pNat place : ℚ) : scalarField place) = (pNat place : scalarField place) := by
      simp
    rw [hcast]
    exact Padic.valuation_p (p := pNat place)
  rw [hval, zpow_neg_one]

theorem padicUnit_norm_one (u : ℤ_[(pNat place)]ˣ) :
    ‖((u : ℤ_[(pNat place)]) : scalarField place)‖ = 1 :=
  PadicInt.norm_units u

theorem padicUnit_valuation_zero (u : ℤ_[(pNat place)]ˣ) :
    (((u : ℤ_[(pNat place)]) : scalarField place)).valuation = 0 := by
  have hprime : (pNat place).Prime :=
    (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2
  have hpgt : (1 : ℝ) < (pNat place : ℝ) := by
    exact_mod_cast hprime.one_lt
  have hnorm := padicUnit_norm_one place u
  have hne : ((u : ℤ_[(pNat place)]) : scalarField place) ≠ 0 := by
    rw [PadicInt.coe_ne_zero]
    exact Units.ne_zero u
  have h := Padic.norm_eq_zpow_neg_valuation (p := pNat place) hne
  rw [hnorm] at h
  have hz : -((((u : ℤ_[(pNat place)]) : scalarField place)).valuation) = 0 :=
    (zpow_eq_one_iff_right₀ (Nat.cast_nonneg (pNat place) : (0 : ℝ) ≤ (pNat place : ℝ))
      hpgt.ne').mp h.symm
  exact neg_eq_zero.mp hz

theorem scalarDVRDecomposition (q : scalarField place) (hq : q ≠ 0) :
    ∃ (m : ℤ) (u : ℤ_[(pNat place)]ˣ),
      q = ((pNat place : ℚ) : scalarField place) ^ m *
        (algebraMap (ℤ_[(pNat place)]) (scalarField place)
          (u : ℤ_[(pNat place)])) := by
  let m : ℤ := q.valuation
  let uq : scalarField place := q * (((pNat place : ℚ) : scalarField place)) ^ (-m)
  have hp_ne : (((pNat place : ℚ) : scalarField place)) ≠ 0 := by
    have hprime : (pNat place).Prime :=
      (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2
    exact_mod_cast hprime.ne_zero
  have hqnorm : ‖q‖ = (pNat place : ℝ) ^ (-m : ℤ) := by
    rw [Padic.norm_eq_zpow_neg_valuation (p := pNat place) hq]
  have ha_ne : (pNat place : ℝ) ≠ 0 := by
    have hprime : (pNat place).Prime :=
      (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2
    exact_mod_cast hprime.ne_zero
  have hinv : (((pNat place : ℝ))⁻¹) ^ (-m) = (pNat place : ℝ) ^ m := by
    rw [← zpow_neg_one, ← zpow_mul, show (-1 : ℤ) * (-m) = m from by ring]
  have hunorm : ‖uq‖ = 1 := by
    show ‖q * (((pNat place : ℚ) : scalarField place)) ^ (-m)‖ = 1
    rw [norm_mul, norm_zpow, hqnorm, scalarPrime_norm place, hinv]
    rw [← zpow_add₀ ha_ne, show -m + m = 0 from by ring, zpow_zero]
  refine ⟨m, PadicInt.mkUnits (p := pNat place) hunorm, ?_⟩
  change q = (((pNat place : ℚ) : scalarField place)) ^ m *
    (algebraMap (ℤ_[(pNat place)]) (scalarField place)
      ((PadicInt.mkUnits (p := pNat place) hunorm : ℤ_[(pNat place)])))
  rw [PadicInt.algebraMap_apply, PadicInt.mkUnits_eq hunorm]
  show q = (((pNat place : ℚ) : scalarField place)) ^ m * uq
  rw [show uq = q * (((pNat place : ℚ) : scalarField place)) ^ (-m) from rfl]
  rw [← mul_assoc (((pNat place : ℚ) : scalarField place) ^ m) q
      (((pNat place : ℚ) : scalarField place) ^ (-m)),
    mul_comm (((pNat place : ℚ) : scalarField place) ^ m) q,
    mul_assoc q (((pNat place : ℚ) : scalarField place) ^ m)
      (((pNat place : ℚ) : scalarField place) ^ (-m))]
  rw [show (((pNat place : ℚ) : scalarField place)) ^ m *
      (((pNat place : ℚ) : scalarField place)) ^ (-m) = 1 from by
    rw [← zpow_add₀ hp_ne, show m + -m = 0 from by ring, zpow_zero]]
  rw [mul_one]

/-! ## Unit upper valuation -/

/-- The actual completion image of a p-adic integral unit has upper valuation
one.  This uses the ramification formula and the lower unit valuation zero. -/
theorem unitUpperValuation (u : ℤ_[(pNat place)]ˣ) :
    (Valued.v (algebraMap (scalarField place) (completionField place)
      (((u : ℤ_[(pNat place)]) : scalarField place))) :
      WithZero (Multiplicative ℤ)) = 1 := by
  let v := (comap (k := ℚ) place).maximalIdeal
  let y : v.adicCompletionIntegers ℚ :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
      (u : ℤ_[(pNat place)])
  have hy_unit : IsUnit y := by
    have hu : IsUnit ((u : ℤ_[(pNat place)])) := ⟨u, rfl⟩
    have h := IsUnit.map
      ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv.toRingHom)
      hu
    simpa [y] using h
  have hy_val : (Valued.v ((y : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) :
      WithZero (Multiplicative ℤ)) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (v := v) (a := y)).mp hy_unit
  have hmap : (algebraMap (scalarField place) (completionField place)
      (((u : ℤ_[(pNat place)]) : scalarField place))) =
      LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place
        (y : v.adicCompletion ℚ) := by
    rw [scalarAlgebra_algebraMap]
    show LeanFormal.IUT.NumberFieldFinitePlace.padicCompletionHom place
        ((u : ℤ_[(pNat place)]) : scalarField place) =
      LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place
        (y : v.adicCompletion ℚ)
    show LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place
        ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (comap (k := ℚ) place).maximalIdeal).symm
          ((u : ℤ_[(pNat place)]) : scalarField place)) =
      LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place
        (y : v.adicCompletion ℚ)
    congr 1
  rw [hmap]
  have hval := LeanFormal.IUT.NumberFieldFinitePlace.valuation_completionMap
    (k := ℚ) (K := F) place (y : v.adicCompletion ℚ)
  rw [hy_val, one_pow] at hval
  exact hval.symm

/-! ## The relation -/

theorem baseScalarValuationRelation (q : scalarField place) (hq : q ≠ 0) :
    ∃ (m : ℤ) (u : ℤ_[(pNat place)]ˣ),
      q = ((pNat place : ℚ) : scalarField place) ^ m *
          (algebraMap (ℤ_[(pNat place)]) (scalarField place)
            (u : ℤ_[(pNat place)])) ∧
        (Valued.v (algebraMap (scalarField place) (completionField place) q) :
          WithZero (Multiplicative ℤ)) =
          WithZero.exp (-(m * (ramification place : ℤ))) := by
  obtain ⟨m, u, hdec⟩ := scalarDVRDecomposition place q hq
  refine ⟨m, u, hdec, ?_⟩
  have hcomp : (algebraMap (scalarField place) (completionField place)
      ((pNat place : ℚ) : scalarField place)) =
      (algebraMap ℚ (completionField place) (pNat place : ℚ)) := by
    have hsym : (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (comap (k := ℚ) place).maximalIdeal).symm
          ((pNat place : ℚ) : scalarField place) =
        ((pNat place : ℚ) : (comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ) :=
      map_ratCast
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (comap (k := ℚ) place).maximalIdeal).symm.toRingHom (pNat place : ℚ)
    calc (algebraMap (scalarField place) (completionField place)
          ((pNat place : ℚ) : scalarField place))
        = LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place
            ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv
              (comap (k := ℚ) place).maximalIdeal).symm
              ((pNat place : ℚ) : scalarField place)) := by
              rw [scalarAlgebra_algebraMap]
              rfl
      _ = LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place
            (((pNat place : ℚ) : (comap (k := ℚ) place).maximalIdeal.adicCompletion ℚ)) := by
              rw [hsym]
      _ = (((pNat place : ℚ) : completionField place)) :=
            map_ratCast (LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place)
              (pNat place : ℚ)
      _ = (algebraMap ℚ (completionField place) (pNat place : ℚ)) :=
            (algebraMap_ratCast_eq' (A := completionField place) (pNat place : ℚ)).symm
  have hunit : (Valued.v (algebraMap (scalarField place) (completionField place)
      (algebraMap (ℤ_[(pNat place)]) (scalarField place)
        (u : ℤ_[(pNat place)]))) : WithZero (Multiplicative ℤ)) = 1 := by
    have h : (algebraMap (ℤ_[(pNat place)]) (scalarField place)
        (u : ℤ_[(pNat place)])) = ((u : ℤ_[(pNat place)]) : scalarField place) :=
      PadicInt.algebraMap_apply _
    rw [h]
    exact unitUpperValuation place u
  rw [hdec]
  simp only [map_mul, map_zpow₀]
  rw [hcomp, upperPrimeValuation place, hunit, mul_one]
  rw [← WithZero.exp_zsmul]
  congr 1
  simp only [zsmul_eq_mul]
  push_cast
  ring

end LeanFormal.IUT.BaseScalarValuationRelation

end
