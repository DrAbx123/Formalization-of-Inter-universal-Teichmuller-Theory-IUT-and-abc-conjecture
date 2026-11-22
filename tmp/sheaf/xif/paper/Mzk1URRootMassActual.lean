/- U-R root mass: the normalized log-mass of the actual root principal lattice.

Route §5.3 J1: for the Kummer relation `r ^ (2*l) = q` in a finite local
extension, the degree-normalized Haar log-mass of the full root lattice `r * O_L`
(not a Haar singleton) equals `log ‖r‖ = (1/(2*l)) * log ‖q‖`.

The proof does not invent a general Haar scaling lemma: it uses
distribHaarChar on the unit group action (built from the actual additive Haar
measure), the actual value-group decomposition `x ^ E = p ^ n * u` with
`‖u‖ = 1` (LocalFieldLogarithm donor), unit-ball invariance, and the
accepted p-scaling donor `measure_prime_smul_finiteDimensional`.

No sorry/axiom/True/PUnit, no heartbeat override. -/
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Algebra.GroupWithZero.Action.Units
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import LeanFormal.IUT.Foundations.LocalFields.PadicFiniteCoordinateHaarScaling
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped Pointwise NNReal ENNReal

namespace LeanFormal.IUT.XiFPaper.Mzk1URRootMassActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

variable {p : Nat} [Fact p.Prime] {L : Type*}
variable [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L]
variable [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
variable [MeasurableSpace L] [BorelSpace L]

/-- Multiplication by a unit of a normed field is continuous; this supplies
`ContinuousConstSMul Lˣ L` for the distributive Haar character. -/
instance urUnitsContinuousConstSMul : ContinuousConstSMul Lˣ L :=
  ⟨fun u => by
    have h : Continuous (fun x : L => (u : L) * x) := continuous_const.mul continuous_id
    simpa only [Units.smul_def, smul_eq_mul] using h⟩

/-- The integral unit ball is the closed unit ball of the norm. -/
theorem integers_eq_closedBall : (Integers L : Set L) = Metric.closedBall (0 : L) 1 := by
  ext x
  have h : (x ∈ (Integers L : Set L)) ↔ ‖x‖ ≤ 1 := mem_integers_iff x
  rw [h, Metric.mem_closedBall, dist_eq_norm, sub_zero]

theorem isOpen_integers : IsOpen (Integers L : Set L) := by
  rw [integers_eq_closedBall]
  exact IsUltrametricDist.isOpen_closedBall (x := (0 : L)) one_ne_zero

theorem isCompact_integers : IsCompact (Integers L : Set L) := by
  rw [integers_eq_closedBall]
  exact isCompact_closedBall 0 1

theorem measure_integers_pos (μ : Measure L) [Measure.IsAddHaarMeasure μ] :
    0 < μ (Integers L : Set L) := by
  have hne : (Integers L : Set L).Nonempty :=
    ⟨(0 : L), by rw [integers_eq_closedBall]; simp⟩
  exact isOpen_integers.measure_pos μ hne

theorem measure_integers_lt_top (μ : Measure L) [Measure.IsAddHaarMeasure μ] :
    μ (Integers L : Set L) < ⊤ :=
  isCompact_integers.measure_lt_top

/-- A norm-one field unit maps the integral unit ball bijectively onto itself. -/
theorem units_smul_integers (w : Lˣ) (hw : ‖(w : L)‖ = 1) :
    w • (Integers L : Set L) = (Integers L : Set L) := by
  have hw0 : (w : L) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  have himg : (fun x : L => (w : L) * x) '' (Integers L : Set L) = (Integers L : Set L) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_integers_iff _).mpr (by
        rw [norm_mul, hw, one_mul]
        exact (mem_integers_iff _).mp (by simpa using hy))
    · intro hx
      refine ⟨(w : L)⁻¹ * x, ?_, ?_⟩
      · exact (mem_integers_iff _).mpr (by
          rw [norm_mul, norm_inv, hw, inv_one, one_mul]
          exact (mem_integers_iff _).mp (by simpa using hx))
      · field_simp
  ext x
  simp only [Set.mem_smul_set, Units.smul_def, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact himg ▸ ⟨y, hy, hxy⟩
  · intro hx
    have hx' : x ∈ (fun z : L => (w : L) * z) '' (Integers L : Set L) := by
      rw [himg]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    exact ⟨y, hy, hyx⟩

/-- The canonical unit inducing multiplication by the rational prime `p`. -/
abbrev urPrimeUnit : Lˣ :=
  Units.map (algebraMap ℚ_[p] L).toMonoidHom
    (LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit (p := p))

theorem urPrimeUnit_val : ((urPrimeUnit (p := p) (L := L) : L)) = (p : L) := by
  simp [urPrimeUnit, LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit]

/-- The distributive Haar character of the rational prime unit is `p^{-D}`. -/
theorem distribHaarChar_urPrimeUnit (μ : Measure L) [Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ] :
    distribHaarChar L (urPrimeUnit (p := p) (L := L)) =
      ((p : ℝ≥0) ^ Module.finrank ℚ_[p] L)⁻¹ := by
  have hOpos := measure_integers_pos (L := L) μ
  have hOfin := measure_integers_lt_top (L := L) μ
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (s := (Integers L : Set L)) (g := urPrimeUnit (p := p) (L := L))
    (r := ((p : ℝ≥0) ^ Module.finrank ℚ_[p] L)⁻¹) hOpos.ne' hOfin.ne ?_
  have hset : urPrimeUnit (p := p) (L := L) • (Integers L : Set L) =
      (p : ℚ_[p]) • (Integers L : Set L) := by
    have hL : urPrimeUnit (p := p) (L := L) • (Integers L : Set L) =
        (fun y : L => (p : L) * y) '' (Integers L : Set L) := by
      ext y
      simp only [Set.mem_smul_set, Set.mem_image, Units.smul_def, smul_eq_mul, urPrimeUnit_val]
    have hR : (p : ℚ_[p]) • (Integers L : Set L) =
        (fun y : L => (p : L) * y) '' (Integers L : Set L) := by
      ext y
      simp only [Set.mem_smul_set, Set.mem_image, Algebra.smul_def, map_natCast]
    rw [hL, hR]
  rw [hset, LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (p := p) μ (Integers L : Set L)]
  have hfactor : ((p : ℝ≥0) ^ Module.finrank ℚ_[p] L) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  rw [ENNReal.coe_inv hfactor, ENNReal.coe_pow, ENNReal.coe_natCast]

/-- A norm-one field unit has trivial distributive Haar character. -/
theorem distribHaarChar_unit_eq_one (μ : Measure L) [Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ] (w : Lˣ) (hw : ‖(w : L)‖ = 1) :
    distribHaarChar L w = 1 := by
  have hOpos := measure_integers_pos (L := L) μ
  have hOfin := measure_integers_lt_top (L := L) μ
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (s := (Integers L : Set L)) (g := w) (r := 1) hOpos.ne' hOfin.ne ?_
  rw [units_smul_integers (L := L) w hw]
  simp

/-- The distributive Haar character of an inverse unit. -/
theorem distribHaarChar_inv (w : Lˣ) :
    distribHaarChar L w⁻¹ = (distribHaarChar L w)⁻¹ := by
  have hchar_ne : (distribHaarChar L w : ℝ≥0) ≠ 0 :=
    (distribHaarChar_pos (A := L) (g := w)).ne'
  have h1 : distribHaarChar L w * distribHaarChar L w⁻¹ = 1 := by
    have h := map_mul (distribHaarChar L) w w⁻¹
    rw [mul_inv_cancel, map_one] at h
    exact h.symm
  refine mul_left_cancel₀ hchar_ne ?_
  rw [mul_inv_cancel₀ hchar_ne]
  exact h1

/-- The distributive Haar character of an integer power of a unit. -/
theorem distribHaarChar_zpow (w : Lˣ) (n : ℤ) :
    distribHaarChar L (w ^ n) = (distribHaarChar L w) ^ n := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, map_pow, zpow_natCast]
  · rw [zpow_neg, zpow_natCast, distribHaarChar_inv, map_pow, zpow_neg, zpow_natCast]

/-- Logarithm of an integer power of a nonnegative real. -/
theorem real_log_nnreal_zpow (a : ℝ≥0) (ha : a ≠ 0) (n : ℤ) :
    Real.log ((a ^ n : ℝ≥0) : ℝ) = (n : ℝ) * Real.log (a : ℝ) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, NNReal.coe_pow, Real.log_pow]
    push_cast
    ring
  · rw [zpow_neg, zpow_natCast, NNReal.coe_inv, NNReal.coe_pow, Real.log_inv, Real.log_pow]
    push_cast
    ring

/-- Logarithm of the distributive Haar character, in terms of the actual field
norm: `log Δ(w) = [L : Q_p] * log ‖w‖`. -/
theorem log_distribHaarChar_eq (μ : Measure L) [Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ] (x : L) (hx : x ≠ 0) :
    Real.log (distribHaarChar L (Units.mk0 x hx) : ℝ) =
      (Module.finrank ℚ_[p] L : ℝ) * Real.log ‖x‖ := by
  classical
  set E : ℕ := logShellRamificationExponent (K := L) (p := p) with hE
  have hEpos : 0 < E := logShellRamificationExponent_pos (K := L) (p := p)
  obtain ⟨n, hn⟩ :=
    exists_norm_pow_logShellRamificationExponent_eq_prime_zpow (K := L) (p := p) x hx
  have hn' : ‖x‖ ^ E = ‖(p : ℚ_[p])‖ ^ n := by
    rw [hE]
    exact hn
  set u : L := ((p : L) ^ n)⁻¹ * x ^ E with hu
  have hp0 : (p : L) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpn0 : ((p : L) ^ n) ≠ 0 := zpow_ne_zero _ hp0
  have hu_ne : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (inv_ne_zero hpn0) (pow_ne_zero _ hx)
  have hu_norm : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_inv, norm_zpow, ← map_natCast (algebraMap ℚ_[p] L) p,
      norm_algebraMap', norm_pow, hn']
    exact inv_mul_cancel₀ (zpow_ne_zero n
      (norm_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)))
  -- unit identity `xU ^ E = pU ^ n * uU`
  have hxU : (Units.mk0 x hx) ^ E = urPrimeUnit (p := p) (L := L) ^ n * Units.mk0 u hu_ne := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, urPrimeUnit_val]
    rw [hu]
    exact (mul_inv_cancel_left₀ hpn0 (x ^ E)).symm
  -- the character power identity
  have hchar_pow : (distribHaarChar L (Units.mk0 x hx)) ^ E =
      (distribHaarChar L (urPrimeUnit (p := p) (L := L))) ^ n := by
    calc (distribHaarChar L (Units.mk0 x hx)) ^ E
        = distribHaarChar L ((Units.mk0 x hx) ^ E) := (map_pow (distribHaarChar L) _ E).symm
      _ = distribHaarChar L (urPrimeUnit (p := p) (L := L) ^ n *
            Units.mk0 u hu_ne) := by rw [hxU]
      _ = distribHaarChar L (urPrimeUnit (p := p) (L := L) ^ n) *
            distribHaarChar L (Units.mk0 u hu_ne) := map_mul (distribHaarChar L) _ _
      _ = (distribHaarChar L (urPrimeUnit (p := p) (L := L))) ^ n * 1 := by
            rw [distribHaarChar_zpow,
              distribHaarChar_unit_eq_one (L := L) μ
                (Units.mk0 u hu_ne) (by simpa using hu_norm)]
      _ = (distribHaarChar L (urPrimeUnit (p := p) (L := L))) ^ n := mul_one _
  have hcharp_ne : (distribHaarChar L (urPrimeUnit (p := p) (L := L)) : ℝ≥0) ≠ 0 :=
    (distribHaarChar_pos (A := L) (g := urPrimeUnit (p := p) (L := L))).ne'
  have hlog_powR :
      (E : ℝ) * Real.log ((distribHaarChar L (Units.mk0 x hx) : ℝ≥0) : ℝ) =
        (n : ℝ) * (-((Module.finrank ℚ_[p] L : ℝ) * Real.log (p : ℝ))) := by
    have hlog := congrArg (fun z : ℝ≥0 => Real.log (z : ℝ)) hchar_pow
    rw [NNReal.coe_pow, Real.log_pow] at hlog
    rw [real_log_nnreal_zpow (distribHaarChar L (urPrimeUnit (p := p) (L := L)))
      hcharp_ne n] at hlog
    rw [distribHaarChar_urPrimeUnit (p := p) (L := L) μ] at hlog
    simp only [NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast] at hlog
    rw [Real.log_inv, Real.log_pow] at hlog
    linarith
  have hlog_norm : (E : ℝ) * Real.log ‖x‖ =
      (n : ℝ) * (-Real.log (p : ℝ)) := by
    have hlog := congrArg Real.log hn
    rw [Real.log_pow, Real.log_zpow, Padic.norm_p, Real.log_inv] at hlog
    linarith
  have hEposR : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hEpos
  have hD : (0 : ℝ) < (Module.finrank ℚ_[p] L : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ_[p]) (M := L)
  have hmain : Real.log ((distribHaarChar L (Units.mk0 x hx) : ℝ≥0) : ℝ) =
      (Module.finrank ℚ_[p] L : ℝ) * Real.log ‖x‖ := by
    have hmul : (E : ℝ) *
        Real.log ((distribHaarChar L (Units.mk0 x hx) : ℝ≥0) : ℝ) =
        (E : ℝ) * ((Module.finrank ℚ_[p] L : ℝ) * Real.log ‖x‖) := by
      rw [hlog_powR]
      calc (n : ℝ) * (-((Module.finrank ℚ_[p] L : ℝ) * Real.log (p : ℝ)))
          = (Module.finrank ℚ_[p] L : ℝ) * ((n : ℝ) * -Real.log (p : ℝ)) := by ring
        _ = (Module.finrank ℚ_[p] L : ℝ) * ((E : ℝ) * Real.log ‖x‖) := by rw [hlog_norm]
        _ = (E : ℝ) * ((Module.finrank ℚ_[p] L : ℝ) * Real.log ‖x‖) := by ring
    exact mul_left_cancel₀ hEposR.ne' hmul
  simpa using hmain

/-- The degree-normalized log-mass of a multiplicative translate of the
integral unit ball equals `log ‖w‖` (the actual root principal lattice,
not a Haar singleton). -/
theorem normalizedLogMass_smul_units (μ : Measure L) [Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ] (w : Lˣ) :
    (1 / (Module.finrank ℚ_[p] L : ℝ)) *
      (Real.log (μ (w • (Integers L : Set L))).toReal -
        Real.log (μ (Integers L : Set L)).toReal) = Real.log ‖(w : L)‖ := by
  have hOpos := measure_integers_pos (L := L) μ
  have hOfin := measure_integers_lt_top (L := L) μ
  have hOtoReal : (μ (Integers L : Set L)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hw0 : (w : L) ≠ 0 := Units.ne_zero w
  have hchar_ne : (distribHaarChar L w : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := L) (g := w)).ne'
  have hD : (0 : ℝ) < (Module.finrank ℚ_[p] L : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ_[p]) (M := L)
  have hμ : μ (w • (Integers L : Set L)) =
      (distribHaarChar L w : ENNReal) * μ (Integers L : Set L) :=
    (distribHaarChar_mul (μ := μ) w (Integers L : Set L)).symm
  have hlogchar := log_distribHaarChar_eq (p := p) (L := L) μ (w : L) hw0
  have hw_eq : Units.mk0 (w : L) hw0 = w := Units.ext rfl
  rw [hw_eq] at hlogchar
  have hlogμ : Real.log (μ (w • (Integers L : Set L))).toReal =
      Real.log (distribHaarChar L w : ℝ) + Real.log (μ (Integers L : Set L)).toReal := by
    rw [hμ, ENNReal.toReal_mul, ENNReal.coe_toReal, Real.log_mul hchar_ne hOtoReal]
  rw [hlogμ, hlogchar]
  field_simp [hD.ne']
  ring

/-- **Kummer root mass.**  For an actual Kummer root `r ^ d = q` the normalized
log-mass of the full root lattice is `(1/d) * log ‖q‖`. -/
theorem normalizedLogMass_kummer_root (μ : Measure L) [Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ] (d : ℕ) (hd : 0 < d) (q : L) (hq : q ≠ 0)
    (r : L) (hr : r ≠ 0) (hroot : r ^ d = q) :
    (1 / (Module.finrank ℚ_[p] L : ℝ)) *
      (Real.log (μ (r • (Integers L : Set L))).toReal -
        Real.log (μ (Integers L : Set L)).toReal) =
      (1 / (d : ℝ)) * Real.log ‖q‖ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- norm relation
  have hnorm_pow : ‖r‖ ^ d = ‖q‖ := by
    have h := congrArg (fun z : L => ‖z‖) hroot
    rw [norm_pow] at h
    exact h
  have hlogr : Real.log ‖r‖ = (1 / (d : ℝ)) * Real.log ‖q‖ := by
    have hlog : (d : ℝ) * Real.log ‖r‖ = Real.log ‖q‖ := by
      rw [← Real.log_pow, hnorm_pow]
    rw [← hlog]
    field_simp
  have hscalar : r • (Integers L : Set L) =
      Units.mk0 r hr • (Integers L : Set L) := by
    rw [Units.smul_mk0]
  rw [hscalar, normalizedLogMass_smul_units (p := p) (L := L) μ (Units.mk0 r hr)]
  rw [show ((Units.mk0 r hr : Lˣ) : L) = r from Units.val_mk0 hr]
  exact hlogr

#print axioms isOpen_integers
#print axioms distribHaarChar_urPrimeUnit
#print axioms log_distribHaarChar_eq
#print axioms normalizedLogMass_smul_units
#print axioms normalizedLogMass_kummer_root

end LeanFormal.IUT.XiFPaper.Mzk1URRootMassActual
end