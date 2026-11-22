import tmp.sheaf.xif.paper.QVFamGlobalProductCarrierActual
import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption

noncomputable section
open scoped BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamGlobalProductCarrierActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2727GlobalQVFamHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b, MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b, BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b, Measure (qVFamTensorBlock T b))
variable [∀ b, Measure.IsAddHaarMeasure (mu b)]
variable [∀ b, SigmaFinite (mu b)]
variable [∀ b, SigmaFinite (mu b)]

/-- The global product unit region: product of the per-b canonical unit references. -/
noncomputable def S2727GlobalUnitRegion : Set (QVFamProductCarrier T) :=
  Set.pi Set.univ (fun b =>
    arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple)

/-- The global product hull interface on the actual mixed-prime carrier. -/
noncomputable def S2727GlobalQVFamHullInterface :
    IQHullLogVolumeInterface (QVFamProductCarrier T) where
  imageSet := globalQPilotRegion T
  hull := globalRootHull T
  imageSet_subset_hull := globalQPilotRegion_subset_globalRootHull T
  logVolume := fun S => globalProductHaar T mu S
  logVolume_mono := by
    intro S U hSU
    exact measure_mono hSU
  unitRegion := S2727GlobalUnitRegion T
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    rw [mem_globalRootHull_iff] at hx
    refine ⟨x, ?_, rfl⟩
    change x ∈ Set.pi Set.univ (fun b =>
      arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple)
    rw [Set.mem_pi]
    intro b _
    have hb := (S2586IQHullLogVolumeInterface (l := l) T b).hull_subset_scaleShift (hx b)
    simpa [S2586IQHullLogVolumeInterface] using hb
  unitRegion_logVolume_lt_top := by
    change (Measure.pi fun b => mu b)
      (Set.pi Set.univ (fun b =>
        arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple)) < ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun b _ =>
      (measure_arithmeticTupleCanonicalRegions_pos_lt_top
        (qVFamTensorPlaces T b) qVFamTensorTuple (mu b)).2.2)
  scaleShift_unitRegion_logVolume_le := by
    show globalProductHaar T mu ((id : QVFamProductCarrier T → QVFamProductCarrier T) ''
        S2727GlobalUnitRegion T) ≤
      globalProductHaar T mu (S2727GlobalUnitRegion T)
    rw [Set.image_id]

#check S2727GlobalUnitRegion
#check S2727GlobalQVFamHullInterface
#print axioms S2727GlobalQVFamHullInterface

end LeanFormal.IUT.XiFPaper.S2727GlobalQVFamHullActual
end