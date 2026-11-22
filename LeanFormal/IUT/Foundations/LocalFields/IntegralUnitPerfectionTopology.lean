import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmOpenMap
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmRationalization
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The topology on actual unit perfection from original units and denominators

Give the integer localization its final topology from the maps taking
an original compact unit to its fraction with each nonzero integer
denominator. The actual logarithmic equivalence is a homeomorphism.
The source topology is defined without reference to that equivalence.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

abbrev unitPerfectionTopology (K : Type*) [NormedField K] [IsUltrametricDist K] :
    TopologicalSpace (UnitLogPerfection K) :=
  ⨆ a : nonZeroDivisors ℤ, TopologicalSpace.coinduced
    (fun u : (Integers K)ˣ =>
      (LocalizedModule.mk (Additive.ofMul u) a : UnitLogPerfection K)) inferInstance

theorem isOpen_unitPerfectionTopology_iff
    {K : Type*} [NormedField K] [IsUltrametricDist K] (s : Set (UnitLogPerfection K)) :
    @IsOpen _ (unitPerfectionTopology K) s ↔
      ∀ a : nonZeroDivisors ℤ, IsOpen
        ((fun u : (Integers K)ˣ =>
          (LocalizedModule.mk (Additive.ofMul u) a : UnitLogPerfection K)) ⁻¹' s) := by
  rw [unitPerfectionTopology, isOpen_iSup_iff]
  rfl

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

theorem unitLogPerfectionEquiv_mk (u : (Integers K)ˣ) (a : nonZeroDivisors ℤ) :
    unitLogPerfectionEquiv (p := p) (LocalizedModule.mk (Additive.ofMul u) a) =
      ((a : ℤ) : K)⁻¹ * unitLog u := by
  have ha : ((a : ℤ) : K) ≠ 0 :=
    Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp a.property)
  have hcancel : (a : ℤ) • (LocalizedModule.mk (Additive.ofMul u) a : UnitLogPerfection K) =
      LocalizedModule.mk (Additive.ofMul u) 1 := by
    letI : Module ℤ (UnitLogPerfection K) :=
      OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
        (S := nonZeroDivisors ℤ) (X := Additive (Integers K)ˣ)
    rw [← Int.cast_smul_eq_zsmul ℤ, LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel a _
  have hvalue := congrArg (unitLogPerfectionEquiv (p := p)) hcancel
  rw [map_zsmul, unitLogPerfectionEquiv_mk_one, zsmul_eq_mul] at hvalue
  rw [← hvalue, inv_mul_cancel_left₀ ha]

def unitLogWithDenominator (a : nonZeroDivisors ℤ) (u : (Integers K)ˣ) : K :=
  ((a : ℤ) : K)⁻¹ * unitLog u

theorem continuous_unitLogWithDenominator (a : nonZeroDivisors ℤ) :
    Continuous (unitLogWithDenominator (K := K) a) :=
  continuous_const.mul (continuous_unitLog (p := p))

theorem isOpenMap_unitLogWithDenominator (a : nonZeroDivisors ℤ) :
    IsOpenMap (unitLogWithDenominator (K := K) a) := by
  have ha : ((a : ℤ) : K) ≠ 0 :=
    Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp a.property)
  exact (Homeomorph.mulLeft₀ (((a : ℤ) : K)⁻¹) (inv_ne_zero ha)).isOpenMap.comp
    (isOpenMap_unitLog (p := p))

theorem isOpen_iff_unitLogWithDenominator_preimage (s : Set K) :
    IsOpen s ↔ ∀ a : nonZeroDivisors ℤ,
      IsOpen (unitLogWithDenominator (K := K) a ⁻¹' s) := by
  constructor
  · intro hs a
    exact hs.preimage (continuous_unitLogWithDenominator (p := p) a)
  · intro hs
    have hcover : s = ⋃ a : nonZeroDivisors ℤ,
        unitLogWithDenominator (K := K) a ''
          (unitLogWithDenominator (K := K) a ⁻¹' s) := by
      ext x
      constructor
      · intro hx
        obtain ⟨a, u, hu⟩ := exists_integer_smul_eq_unitLog (p := p) x
        have ha : ((a : ℤ) : K) ≠ 0 :=
          Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp a.property)
        have heq : unitLogWithDenominator (K := K) a u = x := by
          dsimp only [unitLogWithDenominator]
          rw [← hu, zsmul_eq_mul, inv_mul_cancel_left₀ ha]
        exact Set.mem_iUnion.mpr ⟨a, u, by
          change unitLogWithDenominator (K := K) a u ∈ s
          rw [heq]
          exact hx, heq⟩
      · intro hx
        obtain ⟨a, u, hu, hux⟩ := Set.mem_iUnion.mp hx
        exact hux ▸ hu
    rw [hcover]
    exact isOpen_iUnion (fun a => isOpenMap_unitLogWithDenominator (p := p) a _ (hs a))

def unitLogPerfectionHomeomorph :
    letI := unitPerfectionTopology K
    UnitLogPerfection K ≃ₜ K := by
  letI := unitPerfectionTopology K
  refine { (unitLogPerfectionEquiv (K := K) (p := p)).toEquiv with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_def.mpr
    intro s hs
    apply (isOpen_unitPerfectionTopology_iff _).mpr
    intro a
    change IsOpen ((fun u : (Integers K)ˣ => unitLogPerfectionEquiv (p := p)
      (LocalizedModule.mk (Additive.ofMul u) a)) ⁻¹' s)
    simp_rw [unitLogPerfectionEquiv_mk]
    exact hs.preimage (continuous_unitLogWithDenominator (p := p) a)
  · apply continuous_def.mpr
    intro s hs
    apply (isOpen_iff_unitLogWithDenominator_preimage (p := p) _).mpr
    intro a
    have hs_a := (isOpen_unitPerfectionTopology_iff s).mp hs a
    convert hs_a using 1
    ext u
    simp only [Set.mem_preimage]
    change (unitLogPerfectionEquiv (p := p)).symm
      (((a : ℤ) : K)⁻¹ * unitLog u) ∈ s ↔ _
    rw [← unitLogPerfectionEquiv_mk (p := p), LinearEquiv.symm_apply_apply]

end

end LeanFormal.IUT.LocalFieldLogarithm
