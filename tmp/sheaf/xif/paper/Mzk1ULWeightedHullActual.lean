/- U-L weighted packet hull: actual place weights (local degrees), positivity, and
correct total, then the weighted hull average; no hCor312. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULWeightedHullActual
open LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
/-- Actual weighted packet hull average. -/
noncomputable def ucHpkt {B : Type*} [Fintype B]
    (N : Real) (w : B → Real) (vol : B → Real) : Real :=
  (1 / N) * ∑ b : B, w b * vol b
/-- Weighted packet hull upper from per-b upper bounds and nonnegative weights. -/
theorem ucHpkt_le_bound {B : Type*} [Fintype B]
    (N : Real) (w : B → Real) (vol bound : B → Real)
    (hN : 0 < N) (hw : ∀ b, 0 ≤ w b)
    (h : ∀ b, vol b ≤ bound b) :
    ucHpkt N w vol ≤ (1 / N) * ∑ b : B, w b * bound b := by
  unfold ucHpkt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (h b) (hw b))
/-- The actual divisor weight of a finite place over `p`: the local degree
`[F_v : ℚ_p] = dim_{ℚ_p} F_v`, i.e. the paper's `λ_v = [(F)_v : Q_{vQ}]`. -/
noncomputable def ulDivisorWeight (place : FinitePlaceAtPrime K p) : Real :=
  (Module.finrank ℚ_[p] (CommonPrimeCompletion place) : Real)
/-- The actual divisor weight is nonnegative. -/
theorem ulDivisorWeight_nonneg (place : FinitePlaceAtPrime K p) :
    0 ≤ ulDivisorWeight (p := p) place :=
  Nat.cast_nonneg _
/-- The actual per-tensor-place weight family of a packet. -/
noncomputable def ulPlaceWeight : ι → Real :=
  fun i => ulDivisorWeight (p := p) (places i (tuple i))
/-- Every actual place weight is nonnegative. -/
theorem ulPlaceWeight_nonneg (i : ι) : 0 ≤ ulPlaceWeight (p := p) places tuple i :=
  ulDivisorWeight_nonneg (p := p) (places i (tuple i))
/-- The total weight is exactly the sum of the actual local degrees. -/
theorem ulPlaceWeight_sum :
    (∑ i, ulPlaceWeight (p := p) places tuple i) =
      ∑ i, (Module.finrank ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) : Real) :=
  rfl
/-- The normalized actual weights. -/
noncomputable def ulNormalizedWeight (i : ι) : Real :=
  ulPlaceWeight (p := p) places tuple i /
    ∑ i, ulPlaceWeight (p := p) places tuple i
/-- Normalized actual weights are nonnegative. -/
theorem ulNormalizedWeight_nonneg (hpos : 0 < ∑ i, ulPlaceWeight (p := p) places tuple i)
    (i : ι) : 0 ≤ ulNormalizedWeight (p := p) places tuple i :=
  div_nonneg (ulPlaceWeight_nonneg (p := p) places tuple i) hpos.le
/-- Normalized actual weights have total one. -/
theorem ulNormalizedWeight_sum (hpos : 0 < ∑ i, ulPlaceWeight (p := p) places tuple i) :
    (∑ i, ulNormalizedWeight (p := p) places tuple i) = 1 := by
  unfold ulNormalizedWeight
  rw [← Finset.sum_div]
  exact div_self hpos.ne'
/-- The actual weighted packet hull: the total local degree-normalized sum of the
per-place packet values. -/
noncomputable def ulWeightedPacketHull (W : ι → Real) : Real :=
  ∑ i, ulNormalizedWeight (p := p) places tuple i * W i
/-- The actual weighted packet hull is an average with respect to the actual
normalized weights. -/
theorem ulWeightedPacketHull_eq_average (W : ι → Real)
    (hpos : 0 < ∑ i, ulPlaceWeight (p := p) places tuple i) :
    ulWeightedPacketHull (p := p) places tuple W =
      (∑ i, ulPlaceWeight (p := p) places tuple i * W i) /
        ∑ i, ulPlaceWeight (p := p) places tuple i := by
  unfold ulWeightedPacketHull ulNormalizedWeight
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv]
  ring
/-- The actual weighted packet hull is monotone in the per-place values. -/
theorem ulWeightedPacketHull_le {Vpos Bpos : ι → Real}
    (hVB : ∀ i, Vpos i ≤ Bpos i)
    (hpos : 0 < ∑ i, ulPlaceWeight (p := p) places tuple i) :
    ulWeightedPacketHull (p := p) places tuple Vpos ≤
      ulWeightedPacketHull (p := p) places tuple Bpos := by
  unfold ulWeightedPacketHull
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_left (hVB i) (ulNormalizedWeight_nonneg (p := p) places tuple hpos i))
/-- The unnormalized weighted sum `Σ_a w_a V_a` used by the C3 paper identity. -/
noncomputable def ulWeightedSum (V : ι → Real) : Real :=
  ∑ i, ulPlaceWeight (p := p) places tuple i * V i
/-- The unnormalized weighted sum is bounded by the weighted sum of the
per-place bounds. -/
theorem ulWeightedSum_le {Vpos Bpos : ι → Real}
    (hVB : ∀ i, Vpos i ≤ Bpos i) :
    ulWeightedSum (p := p) places tuple Vpos ≤ ulWeightedSum (p := p) places tuple Bpos := by
  unfold ulWeightedSum
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_left (hVB i) (ulPlaceWeight_nonneg (p := p) places tuple i))
#print axioms ulDivisorWeight_nonneg
#print axioms ulPlaceWeight_nonneg
#print axioms ulPlaceWeight_sum
#print axioms ulNormalizedWeight_sum
#print axioms ulWeightedPacketHull_eq_average
#print axioms ulWeightedPacketHull_le
#print axioms ulWeightedSum_le
end LeanFormal.IUT.XiFPaper.Mzk1ULWeightedHullActual
end
