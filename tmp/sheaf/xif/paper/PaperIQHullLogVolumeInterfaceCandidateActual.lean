import tmp.sheaf.xif.paper.S2823C3NormalizedRegionPosFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.PaperTheta311DataActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

noncomputable section
open scoped BigOperators NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperIQHullLogVolumeInterfaceCandidateActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2823C3NormalizedRegionPosFiniteActual
open LeanFormal.IUT.XiFPaper.PaperTheta311DataActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

universe u

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance candidateMeasurable :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance candidateBorel :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

local instance candidateProper : ProperSpace (C3LogShellTensorBlock C3) := inferInstance
local instance candidateLC : LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

/-- The actual InitialTheta/Theorem 3.11 theta-side data attached to the source
native initial theta data. -/
noncomputable def sourceTheta311Data :
    PaperTheta311ThetaData T.arithmetic :=
  paperTheta311ThetaData T.arithmetic

/-- Candidate `IQHullLogVolumeInterface` from the actual C3 normalized tensor
Haar measure.  The paper image union and holomorphic hull are supplied as
explicit parameters `imageSet`/`hull`, together with their inclusion into the
actual normalized C3 region; these are exactly the still-missing paper
hull/image constructions, and they are not faked as fields.  All other fields
are actual: the normalized C3 log-volume, its monotonicity, the actual
normalized per-place update region as unit region, that region's finiteness,
and identity scale-shift invariance. -/
noncomputable def paperIQHullLogVolumeInterfaceCandidate
    (imageSet hull : Set (C3LogShellTensorBlock C3))
    (hsub : imageSet ⊆ hull)
    (hhull : hull ⊆ C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :
    IQHullLogVolumeInterface (C3LogShellTensorBlock C3) where
  imageSet := imageSet
  hull := hull
  imageSet_subset_hull := hsub
  logVolume := fun S => c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 S
  logVolume_mono := by
    intro S T hST
    exact measure_mono hST
  unitRegion := C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hhull hx, rfl⟩
  unitRegion_logVolume_lt_top :=
    (C3NormalizedRegion_pos_and_finite (l := l) (V := V) (I := I) C3 T e).2
  scaleShift_unitRegion_logVolume_le := by
    rw [Set.image_id]

@[simp] theorem paperIQHullLogVolumeInterfaceCandidate_imageSet
    (imageSet hull : Set (C3LogShellTensorBlock C3))
    (hsub : imageSet ⊆ hull)
    (hhull : hull ⊆ C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :
    (paperIQHullLogVolumeInterfaceCandidate C3 T e imageSet hull hsub hhull).imageSet =
      imageSet := rfl

@[simp] theorem paperIQHullLogVolumeInterfaceCandidate_hull
    (imageSet hull : Set (C3LogShellTensorBlock C3))
    (hsub : imageSet ⊆ hull)
    (hhull : hull ⊆ C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :
    (paperIQHullLogVolumeInterfaceCandidate C3 T e imageSet hull hsub hhull).hull =
      hull := rfl

theorem paperIQHullLogVolumeInterfaceCandidate_unitRegion_logVolume_lt_top
    (imageSet hull : Set (C3LogShellTensorBlock C3))
    (hsub : imageSet ⊆ hull)
    (hhull : hull ⊆ C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :
    (paperIQHullLogVolumeInterfaceCandidate C3 T e imageSet hull hsub hhull).logVolume
        (paperIQHullLogVolumeInterfaceCandidate C3 T e imageSet hull hsub hhull).unitRegion
      < ⊤ :=
  (paperIQHullLogVolumeInterfaceCandidate C3 T e imageSet hull hsub hhull).unitRegion_logVolume_lt_top

#check paperIQHullLogVolumeInterfaceCandidate
#check paperIQHullLogVolumeInterfaceCandidate_unitRegion_logVolume_lt_top
#check sourceTheta311Data

end LeanFormal.IUT.XiFPaper.PaperIQHullLogVolumeInterfaceCandidateActual

end
