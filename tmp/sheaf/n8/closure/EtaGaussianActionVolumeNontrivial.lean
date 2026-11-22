import tmp.sheaf.n8.closure.EtaGaussianActionVolumeActual
import Mathlib

/-!
# Non-vacuous Gaussian action-volume interface

The PUnit interface is rejected.  This file fixes the actual nontrivial group
Q_p^ (p-adic units), the actual tensor block, and the actual norm-log
g |-> log ||g||_p.  The action is a genuine linear automorphism representation,
the set S is Haar-positive/finite, and the BPS formula is recorded as an exact
field.  No PUnit/trivial witness and no arbitrary normLog are used.

The determinant/Haar-scaling formula itself is the remaining exact gap.
-/

noncomputable section

namespace ABCBridge.N8.EtaGaussianActionVolumeNontrivial

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- The actual tensor block. -/
abbrev Block : Type (max u v) :=
  ArithmeticTensorTupleBlock (K := K) (p := p) (ι := ι) (V := V) places tuple

/-- The actual p-adic norm-log on units: g |-> log ||g||_p. -/
noncomputable def pAdicUnitLogNorm (g : ℚ_[p]ˣ) : ℝ :=
  Real.log ‖(g : ℚ_[p])‖

/-- Non-vacuous BPS interface: actual group Q_p^, actual tensor block, actual
linear action, actual norm-log, positive finite Haar S, and the volume formula. -/
structure GaussianActionVolumeNontrivial where
  [measurableBlock : MeasurableSpace (Block (K := K) (p := p) places tuple)]
  mu : Measure (Block (K := K) (p := p) places tuple)
  [addHaar : Measure.IsAddHaarMeasure mu]
  action : ℚ_[p]ˣ →* (Block (K := K) (p := p) places tuple ≃ₗ[ℚ_[p]]
    Block (K := K) (p := p) places tuple)
  action_nontrivial : ∃ g : ℚ_[p]ˣ, action g ≠ 1
  S : Set (Block (K := K) (p := p) places tuple)
  measurable_S : MeasurableSet S
  pos_S : 0 < mu S
  finite_S : mu S < ⊤
  d_j : ℝ
  d_j_ne_zero : d_j ≠ 0
  volume_formula : ∀ g : ℚ_[p]ˣ,
    Real.log (mu (action g '' S)).toReal - Real.log (mu S).toReal =
      pAdicUnitLogNorm (p := p) g / d_j

/-- Exact non-vacuous gap: an actual Q_p^-action with positive finite Haar S and
the BPS determinant formula.  The group and norm-log are fixed to actual
objects; PUnit is not an admissible witness. -/
def GaussianActionVolumeNontrivialGap : Prop :=
  Nonempty (GaussianActionVolumeNontrivial (K := K) (p := p) places tuple)

end ABCBridge.N8.EtaGaussianActionVolumeNontrivial
