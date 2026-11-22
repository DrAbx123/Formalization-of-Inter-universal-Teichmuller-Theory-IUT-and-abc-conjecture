/- R2 construction: actual PacketHullData at (qVFamTensorPlaces, qVFamTensorTuple) from the actual
qVFamily generator, with Phi = {id} and e the unique-index algebra equivalence.
Certifies the StepV (v) box bound for this actual packet hull (paperThetaReadoutB side to follow).
-/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import Mathlib.Algebra.Algebra.Pi

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URActualPacketHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The actual packet-hull data at the qVFam tensor block: Haar measure, e = funUnique.symm,
single slot (), varpi = the actual qVFamily generator, Phi = {id}, exceptional = univ. -/
noncomputable def actualPacketHullData :
    PacketHullData (p := qVFamTensorP T b) (qVFamTensorPlaces T b) qVFamTensorTuple
      (J := Unit) (E := fun _ => qVFamTensorBlock T b) where
  mu := MeasureTheory.Measure.addHaar
  inst := inferInstance
  e := (AlgEquiv.funUnique ℚ_[qVFamTensorP T b] Unit (qVFamTensorBlock T b)).symm
  istar := ()
  varpi := (sourceRootQUnit T b : qVFamTensorBlock T b)
  hvarpi := by
    intro h
    exact (sourceRootQUnit T b).ne_zero h
  Phi := {LinearEquiv.refl ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)}
  hPhi_ne := ⟨LinearEquiv.refl _ _, rfl⟩
  hPhi := by
    intro phi hphi u hu
    have hphi' : phi = LinearEquiv.refl ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) := by
      simpa using hphi
    rw [hphi']
    simpa using hu
  exceptional := Finset.univ
  small_outside := by
    intro i hi
    exact absurd (Finset.mem_univ i) hi

/-- StepV (v) box bound for the actual packet hull. -/
theorem actualPacketHull_normalizedLogVolume_le_box :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        MeasureTheory.Measure.addHaar
        (packetHull (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
          (actualPacketHullData (T := T) (b := b))) ≤
      (-LocalFieldLogarithm.localNormOrder (qVFamTensorP T b)
            (sourceRootQUnit T b : qVFamTensorBlock T b) +
          ∑ i, LocalFieldLogarithm.localNormOrder (qVFamTensorP T b)
            (arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i) +
        1) * Real.log (qVFamTensorP T b : ℝ) +
        ∑ i ∈ (Finset.univ : Finset qVFamTensorV),
          (3 + Real.log (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
            (p := qVFamTensorP T b) : ℝ)) := by
  simpa using packetHull_normalizedLogVolume_le_box
    (p := qVFamTensorP T b) (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (J := Unit) (E := fun _ => qVFamTensorBlock T b)
    (actualPacketHullData (T := T) (b := b))

end LeanFormal.IUT.XiFPaper.Mzk1URActualPacketHullActual
end