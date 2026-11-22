import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

noncomputable section

namespace LeanFormal.IUT.SourceTateParameter

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped WithZero

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The completed integers at the finite place. -/
abbrev CompletionIntegersAt (v : NumberField.FinitePlace K) : Type u :=
  CompletionIntegers v

/-- The DVR maximal-ideal valuation on the completed fraction field agrees with
`Valued.v`.  Equivalently, both have the same valuation ring: the completed
integers. -/
theorem valued_isEquiv_maximalIdealValuation (v : NumberField.FinitePlace K) :
    (Valued.v : Valuation (Completion v) (WithZero (Multiplicative ℤ))).IsEquiv
      ((IsDiscreteValuationRing.maximalIdeal (CompletionIntegers v)).valuation
        (Completion v)) := by
  have hbridge :
      ((Valued.v : Valuation (Completion v) (WithZero (Multiplicative ℤ))).valuationSubring).toSubring
        = Subring.map (algebraMap (CompletionIntegers v) (Completion v)) ⊤ := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
    · rintro ⟨r, -, rfl⟩
      simpa using r.2
  apply Valuation.isEquiv_of_val_le_one
  intro x
  rw [← Valuation.mem_valuationSubring_iff (v := Valued.v) (x := x),
    ← Valuation.mem_valuationSubring_iff
      (v := (IsDiscreteValuationRing.maximalIdeal (CompletionIntegers v)).valuation (Completion v))
      (x := x),
    ← ValuationSubring.mem_toSubring, ← ValuationSubring.mem_toSubring]
  rw [hbridge]
  rw [IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]

/-- Numerical bridge: split multiplicative reduction at the finite place forces
`1 < ||j||` for the local curve. -/
theorem norm_j_gt_one_of_splitMultiplicativeReductionAt
    (X : PuncturedEllipticCurve K) (v : NumberField.FinitePlace K)
    (h : X.HasSplitMultiplicativeReductionAt v) :
    1 < ‖(X.baseChange (Completion v)).jInvariant‖ := by
  rcases h with ⟨C, hC⟩
  let R : Type u := CompletionIntegers v
  let localCurve : PuncturedEllipticCurve (Completion v) := X.baseChange (Completion v)
  let W : WeierstrassCurve (Completion v) := C • localCurve.curve
  haveI : localCurve.curve.IsElliptic := localCurve.isElliptic
  haveI : W.IsElliptic := inferInstance
  have hmult : W.HasMultiplicativeReduction R := hC.toHasMultiplicativeReduction
  have hΔ : (Valued.v W.Δ : WithZero (Multiplicative ℤ)) < 1 :=
    (valued_isEquiv_maximalIdealValuation v).lt_one_iff_lt_one.mpr hmult.badReduction
  have hc4 : (Valued.v W.c₄ : WithZero (Multiplicative ℤ)) = 1 :=
    (valued_isEquiv_maximalIdealValuation v).eq_one_iff_eq_one.mpr
      hmult.multiplicativeReduction
  have hΔnorm : ‖W.Δ‖ < 1 :=
    (Valued.toNormedField.norm_lt_one_iff).mpr hΔ
  have hc4ne : W.c₄ ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hc4
    exact zero_ne_one hc4
  have hc4norm : ‖W.c₄‖ = 1 := by
    have hle : ‖W.c₄‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hc4.le
    have hinv : ‖W.c₄‖⁻¹ ≤ 1 := by
      have hle' : ‖W.c₄⁻¹‖ ≤ 1 :=
        (Valued.toNormedField.norm_le_one_iff).mpr (by
          rw [map_inv₀, hc4, inv_one])
      simpa [norm_inv] using hle'
    have hpos : 0 < ‖W.c₄‖ := norm_pos_iff.mpr hc4ne
    have hone : 1 ≤ ‖W.c₄‖ := by
      rcases (inv_le_one_iff₀ (a := ‖W.c₄‖)).mp hinv with hle0 | hone
      · exact absurd hle0 (not_le_of_gt hpos)
      · exact hone
    exact le_antisymm hle hone
  have hΔne : W.Δ ≠ 0 :=
    (WeierstrassCurve.isUnit_Δ (W := W)).ne_zero
  have hnormj : ‖W.j‖ = ‖W.Δ‖⁻¹ := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
      norm_mul, norm_pow, hc4norm]
    rw [norm_inv]
    norm_num
  have hj : W.j = localCurve.jInvariant := by
    rw [WeierstrassCurve.variableChange_j]
    exact (PuncturedEllipticCurve.jInvariant_spec localCurve).symm
  rw [← hj, hnormj]
  exact (one_lt_inv_iff₀).mpr ⟨norm_pos_iff.mpr hΔne, hΔnorm⟩

end LeanFormal.IUT.SourceTateParameter

end