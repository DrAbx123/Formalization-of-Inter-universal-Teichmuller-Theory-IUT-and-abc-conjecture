/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

/-! # #10: cardinality obstruction for block/product alignment index -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BlockIndexObstructionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem not_nonempty_equiv_of_card_ne {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card α ≠ Fintype.card β) : IsEmpty (α ≃ β) :=
  ⟨fun e => h (Fintype.card_congr e)⟩

theorem tensorCoreWitness_no_index_of_card_ne
    (tuple : (i : ι) → V i) (h : Fintype.card (tensorCoreWitness places tuple).J ≠
      Fintype.card (Bad (nativePlaceSelection T))) :
    IsEmpty ((tensorCoreWitness places tuple).J ≃ Bad (nativePlaceSelection T)) :=
  not_nonempty_equiv_of_card_ne h

end LeanFormal.IUT.XiFPaper.Mzk1BlockIndexObstructionActual
