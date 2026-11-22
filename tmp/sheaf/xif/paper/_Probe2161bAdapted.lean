import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.Foundations.Geometry.GenericNodalReduction
import Mathlib.NumberTheory.Padics.PadicIntegers

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S2687Probe

local instance fact2161 : Fact (Nat.Prime 2161) := ⟨by decide⟩
abbrev L2161 := ℚ_[2161]
abbrev O2161 := ℤ_[2161]

def W2161 : WeierstrassCurve L2161 := WeierstrassCurve.mk 1 0 0 0 5
def W2161Int : WeierstrassCurve O2161 := WeierstrassCurve.mk 1 0 0 0 5

theorem W2161Int_map : W2161Int.map (algebraMap O2161 L2161) = W2161 := rfl

instance : W2161.IsIntegral O2161 := ⟨⟨W2161Int, W2161Int_map⟩⟩

theorem W2161Int_c4 : W2161Int.c₄ = (1 : O2161) := by
  norm_num [W2161Int, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem W2161Int_delta : W2161Int.Δ = (-10805 : O2161) := by
  norm_num [W2161Int, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem W2161Int_delta_mem : W2161Int.Δ ∈ IsLocalRing.maximalIdeal O2161 := by
  rw [W2161Int_delta]
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  rw [show ((-10805 : O2161)) = (( -10805 : ℤ) : O2161) by norm_num]
  exact (PadicInt.norm_intCast_lt_one_iff (p := 2161) (z := (-10805 : ℤ))).2
    (by norm_num : (2161 : ℤ) ∣ -10805)

theorem W2161Int_c4_isUnit : IsUnit W2161Int.c₄ := by
  rw [W2161Int_c4]; exact isUnit_one

theorem W2161_delta_val_lt_one :
    (IsDiscreteValuationRing.maximalIdeal O2161).valuation L2161 W2161.Δ < 1 := by
  rw [← W2161Int_map, WeierstrassCurve.map_Δ]
  change (IsDiscreteValuationRing.maximalIdeal O2161).valuation L2161
    (algebraMap O2161 L2161 W2161Int.Δ) < 1
  exact ((IsDiscreteValuationRing.maximalIdeal O2161).valuation_lt_one_iff_mem
    (K := L2161) W2161Int.Δ).mpr W2161Int_delta_mem

theorem W2161_c4_val_eq_one :
    (IsDiscreteValuationRing.maximalIdeal O2161).valuation L2161 W2161.c₄ = 1 := by
  rw [← W2161Int_map, WeierstrassCurve.map_c₄]
  exact ((IsDiscreteValuationRing.maximalIdeal O2161).valuation_eq_one_iff_notMem
    (K := L2161)).mpr (IsLocalRing.notMem_maximalIdeal.mpr W2161Int_c4_isUnit)

theorem W2161_isMinimal : W2161.IsMinimal O2161 :=
  isMinimal_of_isIntegral_valuation_c₄_eq_one O2161 W2161 W2161_c4_val_eq_one

theorem W2161_hasMul : W2161.HasMultiplicativeReduction O2161 := by
  letI : W2161.IsMinimal O2161 := W2161_isMinimal
  exact { badReduction := W2161_delta_val_lt_one
          multiplicativeReduction := W2161_c4_val_eq_one }

end LeanFormal.IUT.XiFPaper.S2687Probe
end
