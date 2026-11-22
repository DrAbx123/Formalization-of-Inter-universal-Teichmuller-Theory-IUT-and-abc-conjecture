import tmp.sheaf.xif.paper.S3132SharperThetaTargetReductionActual
import tmp.sheaf.xif.paper.S3132ThetaFactorValueActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1800000

noncomputable section
open MeasureTheory

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.S3132ThetaFactorValueActual
open LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual
open LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual

namespace LeanFormal.IUT.XiFPaper.S3132VFormMassRestatementActual

universe u v upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type} {I2 : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I2)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

local instance vformMassMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance vformMassBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual Haar-mass formula for the degree-normalized V-form of the actual
paper hull: `V(hull) = (1/d)(log mu(hull) - log mu(O_hol))`,
`d = finrank_Qp(C3 block)`.  This is definitional (no missing datum) and is the
form in which the residual `MissingVFormCanonicalIdentification` should be
registered: a pure identity between actual Haar masses and the canonical rooted
V-form readout `S3131CanonicalRootedHC T mu` (IUT III, Proposition 3.9, (i),
p. 115; Corollary 3.12, corpus:10324-10353; IUT IV, Proposition 1.4, (i)). -/
theorem c3NormalizedLogVolume_eq_haar_mass_formula :
    c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) =
      (1 / (Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) : ℝ)) *
        (Real.log ((actualC3LogShellTensorHaar C3)
            (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal -
          Real.log ((actualC3LogShellTensorHaar C3)
            (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal) :=
  rfl

/-- **Restated residual (1):** the V-form/canonical identification is exactly the
actual Haar-mass identity `(1/d)(log mu(hull) - log mu(O_hol)) =
S3131CanonicalRootedHC T mu`.  This removes every normalization ambiguity from the
statement: only actual masses and the canonical rooted readout remain. -/
theorem missingVFormCanonicalIdentification_iff_haar_mass_eq :
    MissingVFormCanonicalIdentification C3 T mu ↔
      (1 / (Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) : ℝ)) *
          (Real.log ((actualC3LogShellTensorHaar C3)
              (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal -
            Real.log ((actualC3LogShellTensorHaar C3)
              (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal) =
        S3131CanonicalRootedHC T mu := by
  constructor
  · intro h
    rw [← c3NormalizedLogVolume_eq_haar_mass_formula]
    exact h.vform_eq_canonical
  · intro h
    exact ⟨by rw [c3NormalizedLogVolume_eq_haar_mass_formula]; exact h⟩

/-- **Label-level (d = 1) canonical target criterion.**  If the C3 tensor block
has `Q_p`-rank one and the unit-reference normalization `mu(O_hol) = 1`
(`log mu(O_hol) = 0`) holds, then the exact normalization factor vanishes and the
canonical target is equivalent to the single actual Haar-mass identity
`log mu(hull) = S3131CanonicalRootedHC T mu`. -/
theorem canonicalTarget_iff_log_haar_eq_of_finrank_one_unitReference
    (h1 : Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) = 1)
    (hO : Real.log ((actualC3LogShellTensorHaar C3)
      (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal = 0) :
    thetaPilotHullLogVolumeReal C3 = S3131CanonicalRootedHC T mu ↔
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal =
        S3131CanonicalRootedHC T mu := by
  have hfac : thetaNormalizationFactor C3 = 0 := by
    rw [thetaNormalizationFactor_eq_log_unitReference_of_finrank_one C3 h1]
    exact hO
  have hV : c3NormalizedLogVolume C3
      (actualHolomorphicHull C3 (actualUnitRegion C3)) =
      (1 / (Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) : ℝ)) *
        (Real.log ((actualC3LogShellTensorHaar C3)
            (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal -
          Real.log ((actualC3LogShellTensorHaar C3)
            (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal) :=
    c3NormalizedLogVolume_eq_haar_mass_formula C3
  constructor
  · intro h
    have hraw := thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor C3
    rw [hfac, add_zero, hV, h1] at hraw
    norm_num at hraw
    rw [hO, sub_zero] at hraw
    exact hraw.symm.trans h
  · intro h
    have hraw := thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor C3
    rw [hfac, add_zero, hV, h1] at hraw
    norm_num at hraw
    rw [hO, sub_zero] at hraw
    exact hraw.trans h

#check c3NormalizedLogVolume_eq_haar_mass_formula
#check missingVFormCanonicalIdentification_iff_haar_mass_eq
#check canonicalTarget_iff_log_haar_eq_of_finrank_one_unitReference

end LeanFormal.IUT.XiFPaper.S3132VFormMassRestatementActual

end