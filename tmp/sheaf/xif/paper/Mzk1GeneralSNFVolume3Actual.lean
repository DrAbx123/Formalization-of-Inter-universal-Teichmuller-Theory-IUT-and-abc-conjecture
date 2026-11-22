import tmp.sheaf.xif.paper.Mzk1IndexCardBridgeActual
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula
import tmp.sheaf.xif.paper.Mzk1LatticeOrbitIndexActual

/-! ACTUAL: general SNF volume ratio via A2, normal form on AddSubgroup coercions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1GeneralSNFVolume3Actual
open LeanFormal.IUT.PadicLatticeIndex
open LeanFormal.IUT.XiFPaper.Mzk1LatticeOrbitIndexActual
open LeanFormal.IUT.XiFPaper.Mzk1IndexCardBridgeActual
open Module
variable {p : Nat} [Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (PadicInt p) E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]

theorem general_snf_volume_ratio
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (M : Submodule (PadicInt p) E) {ι : Type*} [Fintype ι]
    (N : Submodule (PadicInt p) M)
    (bM : Module.Basis ι (PadicInt p) M)
    (bN : Module.Basis ι (PadicInt p) N) (a : ι → PadicInt p)
    (hSNF : ∀ i, (bN i : M) = a i • bM i)
    (hMc : IsCompact (M : Set E)) (hMo : IsOpen (M : Set E))
    (hNc : IsCompact ((N.map M.subtype).toAddSubgroup : Set E))
    (hNo : IsOpen ((N.map M.subtype).toAddSubgroup : Set E))
    (hNpos : μ ((N.map M.subtype).toAddSubgroup : Set E) ≠ 0)
    (hNtop : μ ((N.map M.subtype).toAddSubgroup : Set E) ≠ ⊤) :
    (μ ((N.map M.subtype).toAddSubgroup : Set E)).toReal /
      (μ (M.toAddSubgroup : Set E)).toReal =
      (∏ i, (p : ℝ) ^ (a i).valuation)⁻¹ := by
  have hcard : Nat.card (M ⧸ N) = ∏ i, p ^ (a i).valuation :=
    natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm hSNF
  have hbridge := latticeIndex_toAddSubgroup_eq_natCard_quotient (p := p) M N
  have hle_sub : N.map M.subtype ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hle : (N.map M.subtype).toAddSubgroup ≤ M.toAddSubgroup := by
    change (N.map M.subtype).toAddSubmonoid ≤ M.toAddSubmonoid
    exact hle_sub
  have hA := haar_measure_eq_index_mul_of_le μ hle hNc hNo hMc hMo
  have hidx : (latticeIndex ((N.map M.subtype).toAddSubgroup) (M.toAddSubgroup) : ℝ) =
      ∏ i, (p : ℝ) ^ (a i).valuation := by
    rw [hbridge, hcard]; norm_cast
  have hμM : (μ (M.toAddSubgroup : Set E)).toReal =
      (∏ i, (p : ℝ) ^ (a i).valuation) *
        (μ ((N.map M.subtype).toAddSubgroup : Set E)).toReal := by
    have h := congrArg ENNReal.toReal hA
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
    simpa [hidx] using h
  have hN0 : (μ ((N.map M.subtype).toAddSubgroup : Set E)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hNpos hNtop).ne'
  rw [hμM]
  field_simp [hN0]

end LeanFormal.IUT.XiFPaper.Mzk1GeneralSNFVolume3Actual
end