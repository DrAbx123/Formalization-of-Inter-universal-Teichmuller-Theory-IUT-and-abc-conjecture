import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Topology.Basic

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S751HullAdjunctionActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe uX uK uI uV

structure HullAdjunction (X : Type uX) where
  hull : Set X → Set X
  subset_hull : ∀ P, P ⊆ hull P
  hull_mono : ∀ {P Q}, P ⊆ Q → hull P ⊆ hull Q
  hull_idem : ∀ P, hull (hull P) = hull P

theorem hull_fixed (H : HullAdjunction X) (P : Set X) :
    H.hull (H.hull P) = H.hull P :=
  H.hull_idem P

theorem hull_minimal (H : HullAdjunction X) {P Q : Set X}
    (hPQ : P ⊆ Q) (hQ : H.hull Q = Q) : H.hull P ⊆ Q := by
  calc
    H.hull P ⊆ H.hull Q := H.hull_mono hPQ
    _ = Q := hQ

noncomputable def closureHullAdjunction (X : Type uX) [TopologicalSpace X] :
    HullAdjunction X where
  hull := closure
  subset_hull := fun P => subset_closure
  hull_mono := fun h => closure_mono h
  hull_idem := fun P => isClosed_closure.closure_eq

structure HullLogVolumePackage (X : Type uX) (H : HullAdjunction X) where
  muLog : Set X → ENNReal
  muLog_mono : ∀ {P Q : Set X}, P ⊆ Q → muLog P ≤ muLog Q
  finite_hull : ∀ P, muLog (H.hull P) < ⊤

theorem HullLogVolumePackage.logVolume_subset_hull
    {H : HullAdjunction X} (L : HullLogVolumePackage X H) (P : Set X) :
    L.muLog P ≤ L.muLog (H.hull P) :=
  L.muLog_mono (H.subset_hull P)

theorem HullLogVolumePackage.hull_logVolume_mono
    {H : HullAdjunction X} (L : HullLogVolumePackage X H) {P Q : Set X}
    (hPQ : P ⊆ Q) : L.muLog (H.hull P) ≤ L.muLog (H.hull Q) :=
  L.muLog_mono (H.hull_mono hPQ)

variable {p : Nat} [Fact p.Prime]
variable {K : Type uK} [Field K] [NumberField K]
variable {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

noncomputable def arithmeticTupleHullAdjunction :
    HullAdjunction (ArithmeticTensorTupleBlock places tuple) :=
  closureHullAdjunction _

theorem arithmeticTupleNormalizedLogVolume_subset_hull
    (P : Set (ArithmeticTensorTupleBlock places tuple))
    (hpos : 0 < mu P)
    (hfin : mu (closure P) < ⊤) :
    arithmeticTupleNormalizedLogVolume places tuple mu P ≤
      arithmeticTupleNormalizedLogVolume places tuple mu (closure P) :=
  arithmeticTupleNormalizedLogVolume_mono places tuple mu subset_closure hpos hfin

end LeanFormal.IUT.XiFPaper.S751HullAdjunctionActual
end