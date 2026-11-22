/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib.Tactic

/-! # H2 §11.3: saturated minimum / determinant ideal exact interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1H2SaturatedMinimumActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

/-- Exact H2 data on the actual arithmetic packet tensor: source columns,
saturated lattice, determinant ideal and the q-side ideal inclusion. -/
structure H2SaturatedMinimumData where
  sourceSet : Set (ArithmeticPacketTensor places)
  saturatedLattice : Set (ArithmeticPacketTensor places)
  source_subset : sourceSet ⊆ saturatedLattice
  determinantIdeal : Ideal (ArithmeticPacketTensor places)
  qIdeal : Ideal (ArithmeticPacketTensor places)
  ideal_inclusion : qIdeal ≤ determinantIdeal

def H2SaturatedMinimumRequired : Prop := Nonempty (H2SaturatedMinimumData places)

end LeanFormal.IUT.XiFPaper.Mzk1H2SaturatedMinimumActual
