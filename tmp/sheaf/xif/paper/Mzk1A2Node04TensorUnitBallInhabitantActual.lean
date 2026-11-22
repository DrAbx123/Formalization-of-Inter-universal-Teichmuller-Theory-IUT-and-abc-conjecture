/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node04TensorUnitBallInterfaceActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib.Tactic

/-! # A2 node04 §7.3: actual tensor unit-ball inhabitant -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04TensorUnitBallInhabitantActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1A2Node04TensorUnitBallInterfaceActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

/-- Actual tensor-block decomposition from the existing
`arithmeticTensorBlocksAlgEquiv`; the unit ball is the image of the actual
tensor log region under this decomposition. -/
noncomputable def arithmeticTensorUnitBallData :
    A2Node04TensorUnitBallInterface (ArithmeticPacketTensor places)
      ((i : ι) → V i)
      (fun tuple => ArithmeticTensorTupleBlock places tuple) where
  decomposition := (arithmeticTensorBlocksAlgEquiv places).toRingEquiv
  integralLattice := arithmeticTensorLogRegion places
  unitBall := (arithmeticTensorBlocksAlgEquiv places) '' arithmeticTensorLogRegion places
  decomposition_maps_integral := Set.mapsTo_image _ _

theorem arithmeticTensorUnitBallData_nonempty :
    Nonempty (A2Node04TensorUnitBallInterface (ArithmeticPacketTensor places)
      ((i : ι) → V i)
      (fun tuple => ArithmeticTensorTupleBlock places tuple)) :=
  ⟨arithmeticTensorUnitBallData places⟩

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04TensorUnitBallInhabitantActual
