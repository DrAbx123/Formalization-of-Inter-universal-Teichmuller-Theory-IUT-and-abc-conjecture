import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.S706ThetaPilotHullLogActual
import tmp.sheaf.xif.paper.S781TwoLTargetGapActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S788PaperQpilotRegionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

def oneSignedLabel : SignedLabel l.value :=
  ⟨1, by
    constructor
    · have hstar : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · have hstar : (1 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast lStar_ge_one l
      exact hstar⟩

theorem oneSignedLabel_gauss :
    (gaussExponent (oneSignedLabel (l := l)).1).toNat = 1 := by
  unfold oneSignedLabel gaussExponent
  norm_num

noncomputable def paperQPilotRegion : Set (qVFamTensorBlock T b) :=
  rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily T b) oneSignedLabel

noncomputable def paperQPilotLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperQPilotRegion T b)

noncomputable def paperThetaHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperRootCoefficientFamily T b)

theorem paperQPilotRegion_subset_thetaHull :
    paperQPilotRegion T b ⊆
      rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b) := by
  intro x hx
  apply subset_closure
  apply Set.mem_iUnion.mpr
  exact ⟨oneSignedLabel (l := l), hx⟩

theorem paperQPilotLog_le_thetaHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (hpos : 0 < mu (paperQPilotRegion T b))
    (hfin : mu (rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b)) < ⊤) :
    paperQPilotLog T b mu ≤ paperThetaHullLog T b mu :=
  arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperQPilotRegion_subset_thetaHull T b) hpos hfin

noncomputable def paperQPilotGlobalLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperQPilotLog T b Measure.addHaar

noncomputable def paperThetaGlobalHullLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperThetaHullLog T b Measure.addHaar

def PaperTwoLTarget : Prop :=
  paperQPilotGlobalLog T ≤ paperThetaGlobalHullLog T

def S781TwoLTargetLocal : Prop :=
  S706ThetaPilotHullLogActual.globalQPilotLog T ≤ (2 * (l.value : Real)) * S706ThetaPilotHullLogActual.globalThetaPilotHullLog T

theorem paperTwoLTarget_of_perB
    (h : ∀ b : Bad (nativePlaceSelection T),
      paperQPilotLog T b Measure.addHaar ≤ paperThetaHullLog T b Measure.addHaar) :
    PaperTwoLTarget T := by
  unfold PaperTwoLTarget paperQPilotGlobalLog paperThetaGlobalHullLog
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (h b) (nativeBadLocalWeight_nonneg T b)

theorem s781_iff_paperTwoL
    (hq : S706ThetaPilotHullLogActual.globalQPilotLog T = (2 * (l.value : Real)) * paperQPilotGlobalLog T)
    (htheta : S706ThetaPilotHullLogActual.globalThetaPilotHullLog T = paperThetaGlobalHullLog T) :
    S781TwoLTargetLocal T ↔ PaperTwoLTarget T := by
  unfold S781TwoLTargetLocal PaperTwoLTarget
  rw [hq, htheta]
  have h2 : (0 : Real) < 2 * (l.value : Real) := by
    have := l.prime.pos
    positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

end LeanFormal.IUT.XiFPaper.S788PaperQpilotRegionActual
end