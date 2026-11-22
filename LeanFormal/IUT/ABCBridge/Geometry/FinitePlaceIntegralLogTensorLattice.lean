import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralTensorLattice
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The actual integral log-tensor lattice at a tuple of finite places

Each factor is the existing scaled full-unit log-shell in the actual
common-prime completion. Its Zp tensor injects into the genuine Qp tuple
block, with image exactly the compact open integral span. Consequently
the integral tensor has positive finite mass for every actual additive
Haar measure on that block.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm MeasureTheory
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

abbrev arithmeticTupleIntegralLogLattice : Submodule ℤ_[p]
    (ArithmeticTensorTupleBlock places tuple) :=
  tensorLogShellLattice (p := p) (fun i => CommonPrimeCompletion (places i (tuple i)))

abbrev ArithmeticTupleIntegralLogTensor :=
  PiTensorProduct ℤ_[p] (fun i =>
    integralLogShellLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

def arithmeticTupleIntegralLogTensorEquiv :
    ArithmeticTupleIntegralLogTensor places tuple ≃ₗ[ℤ_[p]]
      arithmeticTupleIntegralLogLattice places tuple :=
  integralLogTensorEquivLattice (p := p) _

instance arithmeticTupleIntegralLogLatticeFinite :
    Module.Finite ℤ_[p] (arithmeticTupleIntegralLogLattice places tuple) :=
  tensorLogShellLatticeFinite _

instance arithmeticTupleIntegralLogLatticeFree :
    Module.Free ℤ_[p] (arithmeticTupleIntegralLogLattice places tuple) :=
  tensorLogShellLatticeFree _

theorem isCompact_arithmeticTupleIntegralLogLattice :
    IsCompact (arithmeticTupleIntegralLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) :=
  isCompact_tensorLogShellLattice _

theorem isOpen_arithmeticTupleIntegralLogLattice :
    IsOpen (arithmeticTupleIntegralLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) :=
  isOpen_tensorLogShellLattice _

theorem arithmeticTensorTupleLogRegion_subset_integralLattice :
    arithmeticTensorTupleLogRegion places tuple ⊆
      arithmeticTupleIntegralLogLattice places tuple :=
  tensorLogShellRegion_subset_lattice _

theorem span_padic_arithmeticTupleIntegralLogLattice :
    Submodule.span ℚ_[p] (arithmeticTupleIntegralLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) = ⊤ :=
  padic_span_tensorLogShellLattice_eq_top _

theorem finrank_arithmeticTupleIntegralLogLattice :
    Module.finrank ℤ_[p] (arithmeticTupleIntegralLogLattice places tuple) =
      ∏ i, Module.finrank ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
  (finrank_tensorLogShellLattice (p := p) _).trans
    (finrank_arithmeticTensorTupleBlock places tuple)

theorem finrank_arithmeticTupleIntegralLogTensor :
    Module.finrank ℤ_[p] (ArithmeticTupleIntegralLogTensor places tuple) =
      ∏ i, Module.finrank ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
  (arithmeticTupleIntegralLogTensorEquiv places tuple).finrank_eq.trans
    (finrank_arithmeticTupleIntegralLogLattice places tuple)

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]

theorem measure_arithmeticTupleIntegralLogLattice_pos_lt_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    0 < μ (arithmeticTupleIntegralLogLattice places tuple : Set _) ∧
      μ (arithmeticTupleIntegralLogLattice places tuple : Set _) < ⊤ := by
  have hopen := isOpen_arithmeticTupleIntegralLogLattice places tuple
  exact ⟨Measure.measure_pos_of_nonempty_interior μ
    (by rw [hopen.interior_eq]; exact ⟨0, Submodule.zero_mem _⟩),
    (isCompact_arithmeticTupleIntegralLogLattice places tuple).measure_lt_top⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace
