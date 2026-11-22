import tmp.sheaf.xif.paper.S926GlobalIntegrationActual
import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual

/-! # S942: actual paper S interface

paperSHull D is the paper multiradial S only for the actual paper Ind image D.
An arbitrary/empty indImage is excluded: ActualPaperIndImage requires
nonempty indImage and the Ind1/2/3 transfer fields.  The identification with
the paper Ind image is kept as an exact field, not assumed.  Given this and
the S922 boundedness side condition, the per-b and global weighted
inequalities are actual. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S942ActualPaperSInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S926GlobalIntegrationActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- An actual paper Ind image datum: nonempty, with the three Ind transfers,
and the exact identification with the paper Ind image. -/
structure ActualPaperIndImage (D : PaperIndImageData (l := l) T b) where
  indImage_nonempty : D.indImage.Nonempty
  ind1_transfer : D.ind1_transfer
  ind2_transfer : D.ind2_transfer
  ind3_transfer : D.ind3_transfer
  paperImageIdentification : Prop

/-- Interface for the actual paper multiradial S. -/
structure ActualPaperSInterface where
  D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b
  actualInd : ∀ b : Bad (nativePlaceSelection T),
    ActualPaperIndImage (l := l) T (D b)
  bounded : ∀ b : Bad (nativePlaceSelection T),
    S922IndImageBounded (l := l) T b (D b)
  perB_subset : ∀ b : Bad (nativePlaceSelection T),
    modelHull T b ⊆ paperSHull (l := l) T b (D b)
  perB_le : ∀ b : Bad (nativePlaceSelection T),
    perBModelLog (l := l) T mu b ≤ perBPaperSLog (l := l) T mu D b
  global_le :
    globalModelLog (l := l) T mu ≤ globalPaperSLog (l := l) T mu D

/-- Construct the actual paper S interface from actual Ind image data and the
S922 boundedness side condition; all inequalities are actual. -/
noncomputable def actualPaperSInterfaceOf
    (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b)
    (hactual : ∀ b : Bad (nativePlaceSelection T),
      ActualPaperIndImage (l := l) T (D b))
    (hbounded : ∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (D b)) :
    ActualPaperSInterface T mu where
  D := D
  actualInd := hactual
  bounded := hbounded
  perB_subset := fun b => modelHull_subset_paperSHull (l := l) T b (D b)
  perB_le := perB_le_perB (l := l) T mu D hbounded
  global_le := globalModelLog_le_globalPaperSLog (l := l) T mu D hbounded

/-- The actual paper S interface is nontrivial: every fibre is nonempty. -/
theorem ActualPaperSInterface.indImage_nonempty
    (I : ActualPaperSInterface T mu) (b : Bad (nativePlaceSelection T)) :
    (I.D b).indImage.Nonempty :=
  (I.actualInd b).indImage_nonempty

end LeanFormal.IUT.XiFPaper.S942ActualPaperSInterfaceActual
end
