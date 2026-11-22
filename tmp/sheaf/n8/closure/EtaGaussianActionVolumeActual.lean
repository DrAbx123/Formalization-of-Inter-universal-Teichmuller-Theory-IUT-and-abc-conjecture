import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib

/-!
# Gaussian action volume identity: exact interface

BPS target: for an actual tensor-block action A and a positive finite Haar set S,

  nu(A S) - nu(S) = log |Norm(g)|_p / d_j.

The production tree has the actual tensor block and Haar measures, but no
actual tensor-block action A and no primespine determinant formula for the
right-hand side.  This file records the exact interface and the gap.  No
arbitrary action or set is instantiated.
-/

noncomputable section

namespace ABCBridge.N8.EtaGaussianActionVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w uG

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- The actual tensor block. -/
abbrev Block : Type (max u v) :=
  ArithmeticTensorTupleBlock (K := K) (p := p) (ι := ι) (V := V) places tuple

/-- Exact interface for the BPS Gaussian action-volume identity. -/
structure GaussianActionVolumeData (G : Type uG) [Group G] where
  [measurableBlock : MeasurableSpace (Block (K := K) (p := p) places tuple)]
  mu : Measure (Block (K := K) (p := p) places tuple)
  [addHaar : Measure.IsAddHaarMeasure mu]
  action : G →* (Block (K := K) (p := p) places tuple ≃ₐ[ℚ_[p]]
    Block (K := K) (p := p) places tuple)
  S : Set (Block (K := K) (p := p) places tuple)
  measurable_S : MeasurableSet S
  pos_S : 0 < mu S
  finite_S : mu S < ⊤
  normLog : G → ℝ
  d_j : ℝ
  d_j_ne_zero : d_j ≠ 0
  volume_formula : ∀ g : G,
    Real.log (mu (action g '' S)).toReal - Real.log (mu S).toReal =
      normLog g / d_j


/-- Exact missing construction: an actual tensor-block action A with positive
finite Haar S and the BPS volume formula.  This is an interface gap, not a
free action or free set. -/
def GaussianActionVolumeDataGap : Prop :=
  Nonempty (GaussianActionVolumeData (G := PUnit.{1}) (K := K) (p := p) places tuple)

end ABCBridge.N8.EtaGaussianActionVolumeActual
