import tmp.sheaf.xif.paper.S956PaperTensorClosureActual
import tmp.sheaf.xif.paper.PaperLZetaNormedActual

/-! # S959: topology/Haar data on FinalLValuedCarrier

FinalL = AlgebraicClosure (CommonPrimeCompletion ...), so it is not a
finite-dimensional Qp-space and has no Mathlib locally-compact/Haar instance.
The tensor carrier qVFamBlock ⊗_Qp FinalL has no tensor-product topology
instance either.  The exact minimal topology data is a Qp-linear equivalence
to a finite product of FinalL (for topology/measurable/Borel) together with
local compactness of FinalL (for additive Haar).  No fake locally compact or
Haar instance is asserted.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S959FinalLValuedTopologyExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956PaperTensorClosureActual
open LeanFormal.IUT.XiFPaper.PaperLZetaNormedActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact finite-product topology model: a Qp-linear equivalence of the
tensor carrier to a finite product of FinalL. -/
def S959FiniteProductTopologyModel : Prop :=
  ∃ d : Nat, Nonempty (FinalLValuedCarrier T b ≃ₗ[ℚ_[(qVFamTensorP T b)]]
    (Fin d → FinalL T b))

/-- Exact local compactness input for FinalL. -/
def S959FinalLLocallyCompactRequired : Prop :=
  LocallyCompactSpace (FinalL T b)

/-- Exact topology/measurable input needed before any Haar/log-volume. -/
def S959CarrierTopologyExactInput : Prop :=
  S959FiniteProductTopologyModel (l := l) T b ∧
    S959FinalLLocallyCompactRequired (l := l) T b

/-- The S956 closure hull exists only after a topology is supplied. -/
def S959PaperTensorHullRequiresTopology : Prop :=
  Nonempty (TopologicalSpace (FinalLValuedCarrier T b))

/-- Exact additive-Haar datum after topology/local compactness. -/
structure S959TensorHaarData where
  [addCommGroup : AddCommGroup (FinalLValuedCarrier T b)]
  [topologicalSpace : TopologicalSpace (FinalLValuedCarrier T b)]
  [isTopologicalAddGroup : IsTopologicalAddGroup (FinalLValuedCarrier T b)]
  [locallyCompactSpace : LocallyCompactSpace (FinalLValuedCarrier T b)]
  [measurableSpace : MeasurableSpace (FinalLValuedCarrier T b)]
  [borelSpace : BorelSpace (FinalLValuedCarrier T b)]
  measure : Measure (FinalLValuedCarrier T b)
  [isAddHaar : Measure.IsAddHaarMeasure measure]
  unitRegion : Set (FinalLValuedCarrier T b)
  unit_pos : 0 < measure unitRegion
  unit_lt_top : measure unitRegion < ⊤

def S959TensorHaarDataRequired : Prop :=
  Nonempty (S959TensorHaarData (l := l) T b)

end LeanFormal.IUT.XiFPaper.S959FinalLValuedTopologyExactActual

end
