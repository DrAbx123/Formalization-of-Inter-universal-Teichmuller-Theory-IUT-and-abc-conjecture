import tmp.sheaf.xif.paper.PaperFinalLValuedThetaIndHullActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.MeasureTheory.Measure.Haar.Basic

-- S200: actual finite Ind image hull on FinalLValued, actual qVFam block Haar,
-- and exact gap for Haar/mu_log on the L-valued carrier.
-- No inequality; no fake measure.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperFinalLValuedHaarMuLogGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual finite Ind image hull (Ind1 and the trivial field-unit Ind2/Ind3
-- actions; the full union over all units remains fieldUnitLambdaOHull).
noncomputable def finiteThetaImageIndHull : Set (Carrier T b) :=
  rootThetaImageInLValued T b ∪ ind1Image T b ∪
    ind2Image T b (1 : (FinalL T b)ˣ) ∪
    ind3Image T b (1 : (FinalL T b)ˣ) 0

-- Actual Haar on the qVFam completion block (q side block Haar).
instance qVFamBlockMeasurableSpace : MeasurableSpace (qVFamTensorBlock T b) := borel _

instance qVFamBlockBorelSpace : BorelSpace (qVFamTensorBlock T b) := ⟨rfl⟩

noncomputable def qVFamBlockHaar : Measure (qVFamTensorBlock T b) := Measure.addHaar

-- Exact missing Haar/mu_log API on the L-valued carrier.  The L-valued
-- tensor is not a locally compact completion, so no product Haar is faked.
structure FinalLValuedHaarMuLogGap where
  measurableSpace : MeasurableSpace (Carrier T b)
  haar : @Measure (Carrier T b) measurableSpace
  measurableHull : Prop
  hullPositiveFinite : Prop
  muLog : Set (Carrier T b) → Real
  muLog_eq_logHaar : Prop

def FinalLValuedHaarMuLogGapRequired : Prop :=
  Nonempty (FinalLValuedHaarMuLogGap T b)

#check finiteThetaImageIndHull
#check qVFamBlockHaar
#check FinalLValuedHaarMuLogGap

end LeanFormal.IUT.XiFPaper.PaperFinalLValuedHaarMuLogGapActual

end