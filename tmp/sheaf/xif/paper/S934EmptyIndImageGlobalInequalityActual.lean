import tmp.sheaf.xif.paper.S926GlobalIntegrationActual
import tmp.sheaf.xif.paper.S931IndImageBoundedActual

-- S934: empty Ind image is only an INTERNAL lower bound, not the paper S.
-- The final conditional theorem transfers to an arbitrary supplied paper D
-- when its hull is finite; it does not shrink the paper S to theta-only.
-- If the actual paper Ind image/finiteness is missing, the gap is explicit.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S934EmptyIndImageGlobalInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S926GlobalIntegrationActual
open LeanFormal.IUT.XiFPaper.S931IndImageBoundedActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b)

/-- Empty Ind image family. -/
noncomputable def emptyD :
    ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b :=
  fun b => emptyPaperIndImageData (l := l) T b True True True

theorem emptyD_bounded :
    ∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (emptyD (l := l) T b) :=
  fun b => emptyIndImage_bounded (l := l) T b True True True

theorem paperSHull_empty_subset (b : Bad (nativePlaceSelection T)) :
    paperSHull (l := l) T b (emptyD (l := l) T b) ⊆
      paperSHull (l := l) T b (D b) := by
  unfold paperSHull paperSImageUnion emptyD emptyPaperIndImageData
  apply closure_mono
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact False.elim hx

theorem paperSHull_empty_measure_pos (b : Bad (nativePlaceSelection T)) :
    0 < mu b (paperSHull (l := l) T b (emptyD (l := l) T b)) :=
  lt_of_lt_of_le (modelHull_measure_pos (l := l) T b (mu b))
    (measure_mono (modelHull_subset_paperSHull (l := l) T b (emptyD (l := l) T b)))

/-- INTERNAL lower bound with empty Ind image; NOT the paper S. -/
theorem globalModelLog_le_globalPaperSLog_empty :
    globalModelLog (l := l) T mu ≤
      globalPaperSLog (l := l) T mu (emptyD (l := l) T) :=
  globalModelLog_le_globalPaperSLog (l := l) T mu (emptyD (l := l) T)
    (emptyD_bounded (l := l) T)

/-- Exact finiteness condition for the arbitrary paper hull family. -/
def S934PaperSHullFinite : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    S922PaperSHullFinite (l := l) T b (mu b) (D b)

theorem globalPaperSLog_empty_le_globalPaperSLog
    (hfin : S934PaperSHullFinite (l := l) T mu D) :
    globalPaperSLog (l := l) T mu (emptyD (l := l) T) ≤
      globalPaperSLog (l := l) T mu D := by
  unfold globalPaperSLog
  apply weightedPaperV_mono
  intro b
  unfold perBPaperSLog
  exact arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b)
    qVFamTensorTuple (mu b) (paperSHull_empty_subset (l := l) T D b)
    (paperSHull_empty_measure_pos (l := l) T mu b) (hfin b)

/-- Final global inequality to arbitrary paper D, under finiteness. -/
theorem globalModelLog_le_globalPaperSLog_of_finite
    (hfin : S934PaperSHullFinite (l := l) T mu D) :
    globalModelLog (l := l) T mu ≤
      globalPaperSLog (l := l) T mu D :=
  le_trans (globalModelLog_le_globalPaperSLog_empty (l := l) T mu)
    (globalPaperSLog_empty_le_globalPaperSLog (l := l) T mu D hfin)

#check globalModelLog_le_globalPaperSLog_empty
#check globalModelLog_le_globalPaperSLog_of_finite
#check S934PaperSHullFinite

/-- Exact missing actual paper data: an Ind-image transfer for every b and
finite paper hull.  No inhabitant is asserted. -/
def S934ActualPaperIndImageGap : Prop :=
  ∃ (Dactual : ∀ b : Bad (nativePlaceSelection T),
      PaperIndImageData (l := l) T b),
    (∀ b : Bad (nativePlaceSelection T),
      S931IndImageBoundedActual.IndImageTransferToBlockRequired (l := l) T b (Dactual b)) ∧
      S934PaperSHullFinite (l := l) T mu Dactual

end LeanFormal.IUT.XiFPaper.S934EmptyIndImageGlobalInequalityActual

end