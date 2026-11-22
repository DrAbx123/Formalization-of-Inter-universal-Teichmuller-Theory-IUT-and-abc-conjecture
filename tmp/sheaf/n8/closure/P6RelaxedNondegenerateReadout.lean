import tmp.sheaf.n8.closure.P6RelaxedReadoutActual
import tmp.sheaf.n8.closure.P6FiniteSupportSourceAttempt
import tmp.sheaf.n8.closure.P6NonarchSphereMassActual
import tmp.sheaf.n8.closure.P6ArchReadoutActual

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Nondegenerate relaxed readout: distinct reference and region

Finite branch: reference is the actual closed unit ball, region is the actual
open unit ball.  They are distinct; the difference is the actual nonarch unit
sphere, whose positive mass makes the two Haar masses different and hence the
ellOut nonzero.  Archimedean branch: closed balls of radius 1 and 1/2.

No reference=region is used and no arbitrary weight/region is introduced.
-/

noncomputable section

open MeasureTheory BigOperators Set Metric
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6NonarchSphereMassActual
open LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual
open LeanFormal.IUT.N8Closure.P6FiniteSupportSourceAttempt
open LeanFormal.IUT.N8Closure.P6RelaxedReadoutActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.N8Closure.P6ArchReadoutActual

namespace LeanFormal.IUT.N8Closure.P6RelaxedNondegenerateReadout

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Generic nonarch fact: the closed unit ball mass is the open ball mass plus
the positive unit-sphere mass. -/
theorem closedBall_mass_eq_ball_add_sphere
    {K : Type u} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK] :
    muK (Metric.closedBall (0 : K) 1) =
      muK (Metric.ball (0 : K) 1) + muK (Metric.sphere (0 : K) 1) := by
  rw [← Metric.ball_union_sphere]
  exact measure_union Metric.sphere_disjoint_ball.symm
    (Metric.isClosed_sphere.measurableSet)

/-- Generic nonarch fact: the open unit ball has strictly smaller positive
finite Haar mass than the closed unit ball. -/
theorem ball_mass_lt_closedBall_mass
    {K : Type u} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK] :
    muK (Metric.ball (0 : K) 1) < muK (Metric.closedBall (0 : K) 1) := by
  have hsphere_pos : 0 < muK (Metric.sphere (0 : K) 1) := by
    simpa [Metric.sphere, unitSphere] using
      (unitSphere_measure_pos_lt_top (K := K) muK).1
  have hsphere_ne : muK (Metric.sphere (0 : K) 1) ≠ 0 := hsphere_pos.ne'
  have hball_lt : muK (Metric.ball (0 : K) 1) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : K) 1).measure_lt_top
  rw [closedBall_mass_eq_ball_add_sphere (K := K) muK]
  exact ENNReal.lt_add_right hball_lt.ne hsphere_ne


/-- Finite reference: actual closed unit ball. -/
def finiteRef (v : FinitePlaces (X := X)) : Set (localFieldAt X v.1) :=
  Metric.closedBall (0 : localFieldAt X v.1) 1

/-- Finite region: actual open unit ball (strictly smaller than the reference). -/
def finiteReg (v : FinitePlaces (X := X)) : Set (localFieldAt X v.1) :=
  Metric.ball (0 : localFieldAt X v.1) 1

theorem closedBall_mass_pos_lt_top_at
    (v : FinitePlaces (X := X))
    [IsUltrametricDist (localFieldAt X v.1)]
    [ProperSpace (localFieldAt X v.1)] :
    0 < mu v.1 (Metric.closedBall (0 : localFieldAt X v.1) 1) ∧
      mu v.1 (Metric.closedBall (0 : localFieldAt X v.1) 1) < ⊤ := by
  constructor
  · exact lt_of_lt_of_le (Metric.measure_ball_pos (mu v.1) 0 zero_lt_one)
      (measure_mono Metric.ball_subset_closedBall)
  · exact (isCompact_closedBall (0 : localFieldAt X v.1) 1).measure_lt_top

theorem ball_mass_pos_lt_top_at
    (v : FinitePlaces (X := X))
    [IsUltrametricDist (localFieldAt X v.1)]
    [ProperSpace (localFieldAt X v.1)] :
    0 < mu v.1 (Metric.ball (0 : localFieldAt X v.1) 1) ∧
      mu v.1 (Metric.ball (0 : localFieldAt X v.1) 1) < ⊤ := by
  constructor
  · exact Metric.measure_ball_pos (mu v.1) 0 zero_lt_one
  · exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : localFieldAt X v.1) 1).measure_lt_top

/-- Relaxed finite Adm for the distinct closed/open unit-ball pair. -/
theorem nondegenerateAdm
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    RelaxedAdmFinite (X := X) (mu := mu)
      (fun v => finiteRef (X := X) v) (fun v => finiteReg (X := X) v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact Metric.isClosed_closedBall.measurableSet
  · intro v
    letI : IsUltrametricDist (localFieldAt X v.1) := hultra v.1 v.2
    letI : ProperSpace (localFieldAt X v.1) := hproper v.1 v.2
    exact (closedBall_mass_pos_lt_top_at (X := X) (mu := mu) v).1
  · intro v
    letI : IsUltrametricDist (localFieldAt X v.1) := hultra v.1 v.2
    letI : ProperSpace (localFieldAt X v.1) := hproper v.1 v.2
    exact (closedBall_mass_pos_lt_top_at (X := X) (mu := mu) v).2
  · intro v
    exact measurableSet_ball
  · intro v
    letI : IsUltrametricDist (localFieldAt X v.1) := hultra v.1 v.2
    letI : ProperSpace (localFieldAt X v.1) := hproper v.1 v.2
    exact (ball_mass_pos_lt_top_at (X := X) (mu := mu) v).1
  · intro v
    letI : IsUltrametricDist (localFieldAt X v.1) := hultra v.1 v.2
    letI : ProperSpace (localFieldAt X v.1) := hproper v.1 v.2
    exact (ball_mass_pos_lt_top_at (X := X) (mu := mu) v).2

/-- Nondegenerate relaxed finite readout with distinct reference/region. -/
noncomputable def nondegenerateFiniteReadout
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    RelaxedFiniteReadout (X := X) (mu := mu) := by
  let reference : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1) :=
    fun v => finiteRef (X := X) v
  let region : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1) :=
    fun v => finiteReg (X := X) v
  let support : Finset (FinitePlaces (X := X)) := {badFinitePlace (X := X)}
  refine ⟨support, (finiteWeight (X := X)), (finiteDimension (X := X)),
    finiteDimension_ne_zero (X := X), reference, region, ?_,
    relaxedFiniteEllOut (X := X) (mu := mu) support (finiteWeight (X := X))
      (finiteDimension (X := X)) reference region, rfl⟩
  exact nondegenerateAdm (X := X) (mu := mu) hultra hproper


/-- The nondegenerate finite readout has nonzero value. -/
theorem nondegenerateFiniteReadout_value_ne_zero
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    (nondegenerateFiniteReadout (X := X) (mu := mu) hultra hproper).value ≠ 0 := by
  let v : FinitePlaces (X := X) := badFinitePlace (X := X)
  have hval : (nondegenerateFiniteReadout (X := X) (mu := mu)
      hultra hproper).value =
      relaxedFiniteEllOut (X := X) (mu := mu) {v} (finiteWeight (X := X))
        (finiteDimension (X := X))
        (fun w => finiteRef (X := X) w) (fun w => finiteReg (X := X) w) := rfl
  rw [hval]
  simp only [relaxedFiniteEllOut, Finset.sum_singleton]
  letI : IsUltrametricDist (localFieldAt X v.1) := hultra v.1 v.2
  letI : ProperSpace (localFieldAt X v.1) := hproper v.1 v.2
  have hball := ball_mass_pos_lt_top_at (X := X) (mu := mu) v
  have href := closedBall_mass_pos_lt_top_at (X := X) (mu := mu) v
  have hlt : mu v.1 (finiteReg (X := X) v) <
      mu v.1 (finiteRef (X := X) v) := by
    simpa [finiteReg, finiteRef] using
      (ball_mass_lt_closedBall_mass (K := localFieldAt X v.1) (muK := mu v.1))
  have hne : mu v.1 (finiteReg (X := X) v) ≠
      mu v.1 (finiteRef (X := X) v) := ne_of_lt hlt
  have hApos : 0 < (mu v.1 (finiteReg (X := X) v)).toReal :=
    ENNReal.toReal_pos hball.1.ne' hball.2.ne
  have hBpos : 0 < (mu v.1 (finiteRef (X := X) v)).toReal :=
    ENNReal.toReal_pos href.1.ne' href.2.ne
  have hlog_ne : Real.log (mu v.1 (finiteReg (X := X) v)).toReal -
      Real.log (mu v.1 (finiteRef (X := X) v)).toReal ≠ 0 := by
    intro hz
    have hlogeq : Real.log (mu v.1 (finiteReg (X := X) v)).toReal =
        Real.log (mu v.1 (finiteRef (X := X) v)).toReal := sub_eq_zero.mp hz
    have hAB : (mu v.1 (finiteReg (X := X) v)).toReal =
        (mu v.1 (finiteRef (X := X) v)).toReal :=
      Real.log_injOn_pos hApos hBpos hlogeq
    exact hne ((ENNReal.toReal_eq_toReal_iff' hball.2.ne href.2.ne).mp hAB)
  have hw : finiteWeight (X := X) v ≠ 0 := by
    have hq : 0 < (finitePlaceResidueCardinality
        (F := X.S.arithmetic.Fmod) (finitePrime (X := X) v) : ℝ) := by
      exact_mod_cast finitePlaceResidueCardinality_pos
        (F := X.S.arithmetic.Fmod) (finitePrime (X := X) v)
    exact ne_of_gt (by simpa [finiteWeight] using hq)
  have hd : finiteDimension (X := X) v ≠ 0 :=
    finiteDimension_ne_zero (X := X) v
  exact div_ne_zero (mul_ne_zero hw hlog_ne) hd


/-- Archimedean closed balls of radius 1 and 1/2 have different Haar masses. -/
theorem arch_closedBall_mass_ne
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [ProperSpace E] [Nontrivial E]
    (muE : Measure E) [Measure.IsAddHaarMeasure muE] :
    muE (Metric.closedBall (0 : E) 1) ≠
      muE (Metric.closedBall (0 : E) (1 / 2)) := by
  intro h
  have hbase_pos : 0 < muE (Metric.closedBall (0 : E) 1) := by
    apply Measure.measure_pos_of_nonempty_interior
    exact ⟨0, Metric.ball_subset_interior_closedBall
      (Metric.mem_ball_self zero_lt_one)⟩
  have hbase_fin : muE (Metric.closedBall (0 : E) 1) < ⊤ :=
    (isCompact_closedBall (0 : E) 1).measure_lt_top
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  rw [Measure.addHaar_closedBall' (μ := muE) (x := 0) (r := 1) zero_le_one,
    Measure.addHaar_closedBall' (μ := muE) (x := 0) (r := (1 / 2 : ℝ))
      (by norm_num)] at h
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at h
  have hcancel : ENNReal.ofReal ((1 / 2 : ℝ) ^ Module.finrank ℝ E) = 1 := by
    have h' : muE (Metric.closedBall (0 : E) 1) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ Module.finrank ℝ E) =
        muE (Metric.closedBall (0 : E) 1) * 1 := by
      rw [mul_one, mul_comm (muE (Metric.closedBall (0 : E) 1))]
      rw [← h]
    exact (ENNReal.mul_right_inj hbase_pos.ne' hbase_fin.ne).mp h'
  have hreal : ((1 / 2 : ℝ) ^ Module.finrank ℝ E) = 1 :=
    ENNReal.ofReal_eq_one.mp hcancel
  have hlt : ((1 / 2 : ℝ) ^ Module.finrank ℝ E) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) hd.ne'
  linarith

end LeanFormal.IUT.N8Closure.P6RelaxedNondegenerateReadout

end