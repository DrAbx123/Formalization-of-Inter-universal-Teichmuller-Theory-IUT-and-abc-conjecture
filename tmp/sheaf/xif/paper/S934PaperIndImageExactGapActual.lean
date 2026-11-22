import tmp.sheaf.xif.paper.S931IndImageBoundedActual
import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S934PaperIndImageExactGapActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S931IndImageBoundedActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact paper Ind-image object.  The actual paper S is paperSHull D only for
the actual D; an arbitrary or empty indImage is not the paper target. -/
structure PaperIndImageExactGap where
  D : PaperIndImageData (l := l) T b
  isActualPaperIndImage : Prop
  notThetaOnly : Prop
  bounded : D.indImage ⊆ S922O (l := l) T b

/-- Required exact gap: actual paper Ind image + non-theta-only + O-bound. -/
def PaperIndImageExactGapRequired : Prop :=
  Nonempty (PaperIndImageExactGap (l := l) T b)

/-- Internal lower-bound label: theta-only/empty S is not the paper target. -/
def InternalThetaOnlyLowerBound : Prop :=
  ∃ D : PaperIndImageData (l := l) T b, D.indImage = (∅ : Set (qVFamTensorBlock T b))

/-- The internal lower-bound existence is not the paper Ind image requirement. -/
def PaperIndImageIsActual : Prop :=
  ∃ G : PaperIndImageExactGap (l := l) T b, G.isActualPaperIndImage

end LeanFormal.IUT.XiFPaper.S934PaperIndImageExactGapActual
end