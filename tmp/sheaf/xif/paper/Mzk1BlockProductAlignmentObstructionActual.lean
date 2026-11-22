/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1BlockProductAlignmentActual
import Mathlib.Tactic

/-! # #10: block/product alignment obstruction -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BlockProductAlignmentObstructionActual
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

theorem blockProductAlignment_index_isEmpty_implies
    {tuple : (i : ι) → V i}
    {F : Bad (nativePlaceSelection T) → Type ua}
    [∀ b, NontriviallyNormedField (F b)]
    [∀ b, NormedAlgebra ℚ_[p] (F b)]
    (D : BlockProductAlignmentData places T tuple F)
    (h : IsEmpty (D.W.J ≃ Bad (nativePlaceSelection T))) : False :=
  h.elim D.indexEquiv

end LeanFormal.IUT.XiFPaper.Mzk1BlockProductAlignmentObstructionActual
