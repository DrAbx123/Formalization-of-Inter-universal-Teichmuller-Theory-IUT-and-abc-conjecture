/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1BlockProductAlignmentActual
import Mathlib.Tactic

/-! # #10: cardinality necessary condition for block/product alignment -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BlockAlignmentCardActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1BlockProductAlignmentActual
universe u v w ua
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem card_eq_of_blockProductAlignment
    {tuple : (i : ι) → V i}
    {F : Bad (nativePlaceSelection T) → Type ua}
    [∀ b, NontriviallyNormedField (F b)]
    [∀ b, NormedAlgebra ℚ_[p] (F b)]
    (D : BlockProductAlignmentData places T tuple F)
    [Fintype D.W.J] :
    Fintype.card D.W.J = Fintype.card (Bad (nativePlaceSelection T)) :=
  Fintype.card_congr D.indexEquiv

end LeanFormal.IUT.XiFPaper.Mzk1BlockAlignmentCardActual
