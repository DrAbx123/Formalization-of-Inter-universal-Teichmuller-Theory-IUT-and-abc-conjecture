import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-! # S778: paper qPilot region at the root-half coefficient

The paper qPilot coefficient is order/(2l) = the j=1 theta-region coefficient,
not the classical c_norm=order.  We therefore use
  qPilotPaperRegion := thetaTensorScaledRegion at rootHalfCoefficient,
which is exactly the j=1 root theta region.  It is contained in rootNormHull
by the union definition, and its normalized log is <= the root hull log by
normalized-log monotonicity. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Paper qPilot region: the j=1 theta region at c_root = order/(2l)-coefficient
(rootHalfCoefficient). -/
noncomputable def qPilotPaperRegion : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootHalfCoefficient (l := l) T b)

theorem qPilotPaperRegion_eq_rootThetaRegion_one :
    qPilotPaperRegion (l := l) T b =
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) (oneLabel l) := by
  unfold qPilotPaperRegion rootThetaRegion
  congr 1
  funext i
  rw [gaussExponent_oneLabel]
  ring

/-- The normalized qPilot region is contained in the paper half-coefficient
region, because c_half <= c_norm and fractional lattices reverse this order. -/
theorem qPilotNormRegion_subset_qPilotPaperRegion :
    qPilotNormRegion (l := l) T b ⊆ qPilotPaperRegion (l := l) T b := by
  intro x hx
  unfold qPilotNormRegion qPilotClassicalRegion qPilotPaperRegion
    thetaTensorScaledRegion at *
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (rootNormCoefficient (l := l) T b) <=
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (rootHalfCoefficient (l := l) T b) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    exact rootHalfCoefficient_le_norm (l := l) T b i
  exact (mul_le_mul' hlat le_rfl) hx

/-- The paper qPilot region is contained in rootNormHull: it is the j=1
member of the root theta union. -/
theorem qPilotPaperRegion_subset_rootNormHull :
    qPilotPaperRegion (l := l) T b ⊆ rootNormHull (l := l) T b := by
  rw [qPilotPaperRegion_eq_rootThetaRegion_one]
  unfold rootNormHull rootThetaHull rootThetaImageSet
  intro x hx
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨oneLabel l, hx⟩

theorem qPilotPaperRegion_measure_pos :
    0 < mu (qPilotPaperRegion (l := l) T b) :=
  lt_of_lt_of_le
    (qPilotNormRegion_measure_pos_lt_top (l := l) T b mu).1
    (measure_mono (qPilotNormRegion_subset_qPilotPaperRegion (l := l) T b))

/-- Paper qPilot log: normalized log of the half-coefficient region. -/
noncomputable def qPilotPaperLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (qPilotPaperRegion (l := l) T b)

/-- Actual comparison: paper qPilot log <= root hull theta log. -/
theorem qPilotPaperLog_le_thetaLog :
    qPilotPaperLog (l := l) T b mu ≤
      rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootHalfCoefficient (l := l) T b) := by
  unfold qPilotPaperLog rootThetaHullLog
  apply arithmeticTupleNormalizedLogVolume_mono
  · exact qPilotPaperRegion_subset_rootNormHull (l := l) T b
  · exact qPilotPaperRegion_measure_pos (l := l) T b mu
  · exact rootNormHull_measure_lt_top (l := l) T b mu

/-- Exact missing formula datum: the paper qPilot log equals
-(sum c_root)*log p, i.e. the scaling data at the half coefficient. -/
def PaperQPilotLogFormulaIdentification : Prop :=
  qPilotPaperLog (l := l) T b mu =
    -((∑ i, rootHalfCoefficient (l := l) T b i) *
      Real.log (qVFamTensorP T b : Real))

def PaperQPilotLogFormulaIdentificationRequired : Prop :=
  PaperQPilotLogFormulaIdentification (l := l) T b mu

end LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
end
