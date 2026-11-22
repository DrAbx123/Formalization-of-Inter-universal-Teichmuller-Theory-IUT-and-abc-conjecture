/- R2 REAL ROW V/H WIRING (owner: henry; route doc §4.2 steps 1-4).
Provides: (1) the real row-volume `rowV` = actual `packetHull` normalized log volume
(kurt's row V), (2) the total readout `H = Σ_b w_b · avg_j V_bj` with its definitional
identity, (3) the weighted monotone bound `H ≤ Σ_b w_b · avg_j B_bj` from per-row bounds
(NO union-volume ≤ average shortcut), and (4) the `processionNormalized_le_of_distinguishedBounds`
path (alias of the DONE `Mzk1BoxStepVAverageActual.stepV_procession_le_of_distinguished`).
REUSE (DONE): `Mzk1BoxReadoutLocalActual.{packetHull, PacketHullData}`,
`Mzk1G1F2R2RowVAssemblyActual.rowV_le_collectionChoiceBound`,
`Mzk1BoxStepVAverageActual.stepV_procession_le_of_distinguished`.
No fake equality; H is defined by the weighted row average. -/
import tmp.sheaf.xif.paper.Mzk1G1F2R2RowVAssemblyActual
import tmp.sheaf.xif.paper.Mzk1BoxStepVAverageActual
import Mathlib.Tactic

set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

noncomputable section
namespace LeanFormal.IUT.XiFPaper.R2RowVActual
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable {places : (i : ι) → V i → FinitePlaceAtPrime K p} {tuple : (i : ι) → V i}
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

/-- **Real row volume** `V = ν(packetHull D)` (kurt's row V): the actual normalized Haar
log-volume of the packet hull. -/
noncomputable def rowV (D : LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual.PacketHullData
    (J := J) (E := E) places tuple) : ℝ :=
  arithmeticTupleNormalizedLogVolume places tuple D.mu
    (LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual.packetHull (J := J) (E := E) D)

/-- `V` is definitionally the packet-hull normalized log volume. -/
theorem rowV_eq (D : LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual.PacketHullData
    (J := J) (E := E) places tuple) :
    rowV (J := J) (E := E) (p := p) D =
      arithmeticTupleNormalizedLogVolume places tuple D.mu
        (LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual.packetHull (J := J) (E := E) D) := rfl
/-- **Total readout** `H = Σ_b w_b · avg_j V_bj` over a finite bad index `b` and label index `j`. -/
noncomputable def HTotal {β : Type*} [Fintype β] {Label : Type*} [Fintype Label]
    (w : β → ℝ) (Vbj : β → Label → ℝ) : ℝ :=
  ∑ b, w b * ((∑ j, Vbj b j) / (Fintype.card Label : ℝ))

/-- `H` is definitionally the weighted row average `Σ_b w_b · avg_j V_bj`. -/
theorem HTotal_eq {β : Type*} [Fintype β] {Label : Type*} [Fintype Label]
    (w : β → ℝ) (Vbj : β → Label → ℝ) :
    HTotal w Vbj = ∑ b, w b * ((∑ j, Vbj b j) / (Fintype.card Label : ℝ)) := rfl

/-- **Unit-label specialization**: `H = Σ_b w_b·v_b` when the label index is `Unit`.
This is the exact shape of the `Mzk1URThetaKC3UpperActual` inputs (`thetaLamWeight`, `urPacketV_K`):
its `hstepVIII` LHS is `∑ b, thetaLamWeight T b * urPacketV_K T b`,
which is this `HTotal` at `Label := Unit`. -/
theorem HTotal_unit_eq {β : Type*} [Fintype β] (w v : β → ℝ) :
    HTotal (Label := Unit) w (fun b _ => v b) = ∑ b, w b * v b := by
  unfold HTotal
  simp
/-- **Weighted monotone bound**: per-row bounds `V_bj ≤ B_bj` give the total bound
`H ≤ Σ_b w_b · avg_j B_bj` when weights are nonnegative.  This is the legal inequality
direction (no union-volume ≤ average shortcut). -/
theorem HTotal_le_of_rowBound {β : Type*} [Fintype β] {Label : Type*} [Fintype Label]
    [Nonempty Label] (w : β → ℝ) (Vbj Bbj : β → Label → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hV : ∀ b j, Vbj b j ≤ Bbj b j) :
    HTotal w Vbj ≤ ∑ b, w b * ((∑ j, Bbj b j) / (Fintype.card Label : ℝ)) := by
  unfold HTotal
  refine Finset.sum_le_sum (fun b _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (hw b)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact Finset.sum_le_sum (fun j _ => hV b j)

/-- **R2 path**: the paper procession bound from distinguished-slot bounds (DONE donor). -/
theorem processionNormalized_le_of_distinguishedBounds_path
    {E : Type u} [Fintype E] [Nonempty E]
    (n : Nat) (n_ge_two : 2 ≤ n)
    (lam : E → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (logp iotaL : ℝ) (d oq : E → ℝ)
    (different_nonneg : 0 ≤ (∑ e, d e * logp * lam e) / ∑ e, lam e)
    (logp_nonneg : 0 ≤ logp) (iotaL_nonneg : 0 ≤ iotaL)
    (slot : (j : Nat) → Fin (j + 1))
    (Vrow : (j : Nat) → (Fin (j + 1) → E) → ℝ)
    (bound : ∀ j ∈ Finset.Icc 1 n, ∀ et,
      Vrow j et ≤
        LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound
          (2 * (n : ℝ) + 1) logp iotaL j d oq et (slot j)) :
    1 / (n : ℝ) * ∑ j ∈ Finset.Icc 1 n,
      (∑ et : Fin (j + 1) → E, Vrow j et * ∏ i, lam (et i)) /
        (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) ≤
    (2 * (n : ℝ) + 1 + 1) / 4 *
      ((1 + 4 / (2 * (n : ℝ) + 1)) * ((∑ e, d e * logp * lam e) / (∑ e, lam e)) -
        ((∑ e, oq e * logp * lam e) / (∑ e, lam e)) / 6 +
        (4 / (2 * (n : ℝ) + 1)) * logp + (20 / 3) * iotaL) :=
  LeanFormal.IUT.XiFPaper.Mzk1BoxStepVAverageActual.stepV_procession_le_of_distinguished
    n n_ge_two lam weights_pos logp iotaL d oq different_nonneg logp_nonneg iotaL_nonneg
    slot Vrow bound

#print axioms rowV_eq
#print axioms HTotal_eq
#print axioms HTotal_unit_eq
#print axioms HTotal_le_of_rowBound
#print axioms processionNormalized_le_of_distinguishedBounds_path
end LeanFormal.IUT.XiFPaper.R2RowVActual