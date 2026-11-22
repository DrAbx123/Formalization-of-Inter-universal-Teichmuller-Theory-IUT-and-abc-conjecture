/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
import Mathlib.Tactic

/-! # #10: actual witness of the P3 tensor-core field decomposition -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

/-- Actual witness of the tensor-core field-product decomposition. -/
structure TensorCoreWitness (tuple : (i : ι) → V i) where
  J : Type (max u v)
  [fintype : Fintype J]
  E : J → Type (max u v)
  [field : ∀ j, NontriviallyNormedField (E j)]
  [alg : ∀ j, NormedAlgebra ℚ_[p] (E j)]
  equiv : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)
  finite : ∀ j, FiniteDimensional ℚ_[p] (E j)

theorem tensorCoreWitness_nonempty (tuple : (i : ι) → V i) :
    Nonempty (TensorCoreWitness places tuple) := by
  rcases tensorCore_fieldProduct places tuple with ⟨J, hJ, E, hfield, halg, e, hfin⟩
  letI : Fintype J := hJ
  letI : ∀ j, NontriviallyNormedField (E j) := hfield
  letI : ∀ j, NormedAlgebra ℚ_[p] (E j) := halg
  exact ⟨{ J := J, fintype := hJ, E := E, field := hfield, alg := halg, equiv := e, finite := hfin }⟩

noncomputable def tensorCoreWitness (tuple : (i : ι) → V i) :
    TensorCoreWitness places tuple :=
  Classical.choice (tensorCoreWitness_nonempty places tuple)

end LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
