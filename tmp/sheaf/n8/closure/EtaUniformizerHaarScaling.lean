import tmp.sheaf.n8.closure.EtaHaarCharNormIdentification
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

/-!
# Eta uniformizer / norm-one unit Haar scaling

Actual p-scalar scaling is already proved.  Here we prove the integral-unit
case: for u in (Integers K)^x, the corresponding unit of K has mK(u)=1, because
multiplication by u preserves the integer ball O = Integers K.

The uniformizer/general-q scaling is recorded as an exact target.  The
production uniformizer norm theorem is imported, but no arbitrary factor is
introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.overlappingInstances false

namespace LeanFormal.IUT.N8Closure.EtaUniformizerHaarScaling

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Pointwise
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration
open LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]
  {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- An integral unit of K. -/
def integerUnitInK (u : (Integers K)ˣ) : Kˣ :=
  Units.map (Integers K).subtype.toMonoidHom u

theorem integerUnitInK_val (u : (Integers K)ˣ) :
    ((integerUnitInK (K := K) u : Kˣ) : K) = (u.val : K) := rfl

/-- Multiplication by an integral unit preserves O = Integers K. -/
theorem integerUnit_smul_O (u : (Integers K)ˣ) :
    integerUnitInK (K := K) u • O K = O K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ‖y‖ ≤ 1 := (mem_integers_iff y).mp (by simpa [O] using hy)
    change ‖(integerUnitInK (K := K) u : K) * y‖ ≤ 1
    rw [integerUnitInK_val, norm_mul, norm_unit_eq_one (K := K) u, one_mul]
    exact hy'
  · intro hx
    have hx' : ‖x‖ ≤ 1 := (mem_integers_iff x).mp (by simpa [O] using hx)
    refine ⟨((integerUnitInK (K := K) u)⁻¹ : K) • x, ?_, ?_⟩
    · change ‖((↑(integerUnitInK (K := K) u) : K)⁻¹ * x)‖ ≤ 1
      have hu_inv : ((↑(integerUnitInK (K := K) u) : K)⁻¹) =
          ((u⁻¹).val : K) := by
        rw [integerUnitInK_val]
        exact (map_units_inv (Integers K).subtype.toMonoidHom u).symm
      rw [hu_inv, norm_mul, norm_unit_eq_one (K := K) (u⁻¹), one_mul]
      exact hx'
    · simp [Units.smul_def]

/-- Actual mK of an integral unit is 1. -/
theorem mK_integerUnit (u : (Integers K)ˣ) :
    mK (K := K) (integerUnitInK (K := K) u) = 1 := by
  let μ : Measure K := Measure.addHaar
  have hO := measure_O_pos_lt_top (K := K) μ
  have hmeasure : μ (integerUnitInK (K := K) u • O K) = (1 : ENNReal) * μ (O K) := by
    rw [integerUnit_smul_O (K := K) u]
    simp
  have hchar : (distribHaarChar K) (integerUnitInK (K := K) u) = 1 :=
    distribHaarChar_eq_of_measure_smul_eq_mul (A := K) (μ := μ)
      hO.1.ne' hO.2.ne hmeasure
  unfold mK
  rw [hchar]
  norm_num

/-- Exact uniformizer Haar target: mK(π) = ||π||^d. -/
def UniformizerHaarTarget (π : Kˣ) : Prop :=
  mK (K := K) π =
    (‖(π : K)‖ : Real) ^ localDimension (K := K) (p := p)

/-- The general q scaling target remains the same exact norm-power statement. -/
def GeneralQHaarTarget : Prop :=
  HaarNormIdentificationTarget (K := K) (p := p)

/-- Missing production data: a uniformizer theorem identifying the Haar
character of an arbitrary local uniformizer with its norm power, or the
general norm-one-unit scaling theorem. -/
structure EtaUniformizerMissingData where
  uniformizer_power_relation :
    ∀ (π : Integers K), Irreducible π →
      ∃ (u : (Integers K)ˣ) (n : Nat),
        (p : K) = (u.val : K) * ((π : K) ^ n)
  norm_power_identification :
    ∀ π : Kˣ, UniformizerHaarTarget (K := K) (p := p) π

end LeanFormal.IUT.N8Closure.EtaUniformizerHaarScaling
