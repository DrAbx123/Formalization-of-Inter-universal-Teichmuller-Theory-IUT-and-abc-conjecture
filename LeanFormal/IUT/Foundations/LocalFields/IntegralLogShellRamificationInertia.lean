import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Ramification and inertia data for the log-shell residue field

This file builds the local `q/e/f` invariants on top of the proved
residue-field finiteness in `IntegralLogShellIndexResidueFormula`.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]

instance normedFieldValuationHasExtension :
    (NormedField.valuation (K := Padic p)).HasExtension
      (NormedField.valuation (K := K)) where
  val_isEquiv_comap := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    simp only [Valuation.comap_apply, NormedField.valuation_apply]
    rw [nnnorm_algebraMap']

instance integersAlgebra : Algebra (Integers (Padic p)) (Integers K) :=
  inferInstance

example : IsLocalHom (algebraMap (Integers (Padic p)) (Integers K)) := inferInstance

/-- The image of the rational prime `p` in `K` has norm strictly below one. -/
theorem norm_prime_lt_one : ‖(p : K)‖ < 1 := by
  rw [← algebraMap.coe_natCast (R := Padic p) (A := K) p, norm_algebraMap']
  simpa using Padic.norm_p_lt_one (p := p)

/-- The rational prime is nonzero in the valuation ring. -/
theorem prime_ne_zero_integers : (p : Integers K) ≠ 0 := by
  intro h
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  apply hpK
  simpa using congrArg (fun x : Integers K => (x : K)) h

include p

/-- Properness supplies the discrete valuation ring structure on the actual
integer ring. No additional DVR hypothesis is assumed. -/
theorem isDiscreteValuationRingIntegers : IsDiscreteValuationRing (Integers K) := by
  letI : CompactSpace (Integers K) :=
    isCompact_iff_compactSpace.mp (isCompact_valuationIntegerLattice (K := K) (p := p))
  have hpnorm : ‖(p : K)‖ < 1 := norm_prime_lt_one (K := K) (p := p)
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  letI : NontriviallyNormedField K :=
    NontriviallyNormedField.ofNormNeOne ⟨(p : K), hpne, ne_of_lt hpnorm⟩
  have hn : (Valued.v : Valuation K ℝ≥0).IsNontrivial :=
    (Valuation.isNontrivial_iff_exists_lt_one
      (v := (Valued.v : Valuation K ℝ≥0))).mpr
      ⟨(p : K), hpne, by
        rw [NormedField.v_eq_valuation, NormedField.valuation_apply]
        rw [← NNReal.coe_lt_coe]
        simpa using hpnorm⟩
  letI : (Valued.v : Valuation K ℝ≥0).IsNontrivial := hn
  exact Valued.integer.isDiscreteValuationRing_of_compactSpace (K := K) (Γ₀ := ℝ≥0)

/-- The additive valuation of the rational prime, evaluated at the DVR structure
constructed from properness. This makes the instance argument explicit so that
the statement is independent of typeclass search for the ambient prime. -/
noncomputable def ramifiedPrimeAddVal : ℕ∞ :=
  @IsDiscreteValuationRing.addVal (Integers K) _ _
    (isDiscreteValuationRingIntegers (K := K) (p := p)) (p : Integers K)

/-- The additive valuation of the rational prime: the ramification exponent
`e = v_K(p)`, normalised so that a uniformiser has valuation one. -/
def logShellRamificationExponent : Nat :=
  (ramifiedPrimeAddVal (K := K) (p := p)).toNat

/-- The additive valuation of `p` is finite. -/
theorem addVal_prime_ne_top :
    ramifiedPrimeAddVal (K := K) (p := p) ≠ ⊤ := by
  unfold ramifiedPrimeAddVal
  intro htop
  rw [@IsDiscreteValuationRing.addVal_eq_top_iff (Integers K) _ _
    (isDiscreteValuationRingIntegers (K := K) (p := p)) (p : Integers K)] at htop
  exact prime_ne_zero_integers (K := K) (p := p) htop

/-- The `Nat` ramification exponent is exactly the additive valuation of `p`. -/
theorem addVal_prime_eq_ramificationExponent :
    ramifiedPrimeAddVal (K := K) (p := p) =
      (logShellRamificationExponent (K := K) (p := p) : ℕ∞) := by
  unfold logShellRamificationExponent ramifiedPrimeAddVal
  exact (ENat.coe_toNat (addVal_prime_ne_top (K := K) (p := p))).symm

/-- The ramification exponent is positive. -/
theorem logShellRamificationExponent_pos :
    0 < logShellRamificationExponent (K := K) (p := p) := by
  unfold logShellRamificationExponent ramifiedPrimeAddVal
  apply ENat.toNat_pos
  · intro hzero
    rw [@IsDiscreteValuationRing.addVal_eq_zero_iff (Integers K) _ _
      (isDiscreteValuationRingIntegers (K := K) (p := p)) (p : Integers K)] at hzero
    rcases hzero with ⟨u, hu⟩
    have hnorm := norm_unit_eq_one (K := K) u
    have hpnorm : ‖(p : K)‖ < 1 := norm_prime_lt_one (K := K) (p := p)
    have hcoe : ((u : Integers K) : K) = (p : K) := by
      simpa using congrArg (fun x : Integers K => (x : K)) hu
    rw [hcoe] at hnorm
    linarith
  · exact addVal_prime_ne_top (K := K) (p := p)

end

end LeanFormal.IUT.LocalFieldLogarithm
