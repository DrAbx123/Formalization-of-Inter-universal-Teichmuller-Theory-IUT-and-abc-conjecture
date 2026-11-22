/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic

/-! # #10: block product alignment data and assembly -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1BlockProductAlignmentActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
universe u v w ua
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

structure BlockProductAlignmentData (tuple : (i : ι) → V i)
    (F : Bad (nativePlaceSelection T) → Type ua)
    [∀ b, NontriviallyNormedField (F b)]
    [∀ b, NormedAlgebra ℚ_[p] (F b)] where
  W : TensorCoreWitness places tuple
  [fintypeW : Fintype W.J]
  [fieldW : ∀ j, NontriviallyNormedField (W.E j)]
  [algW : ∀ j, NormedAlgebra ℚ_[p] (W.E j)]
  indexEquiv : W.J ≃ Bad (nativePlaceSelection T)
  factorEquiv : ∀ j, W.E j ≃ₐ[ℚ_[p]] F (indexEquiv j)

end LeanFormal.IUT.XiFPaper.Mzk1BlockProductAlignmentActual
