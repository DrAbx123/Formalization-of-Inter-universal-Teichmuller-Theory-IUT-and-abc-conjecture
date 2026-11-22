import tmp.sheaf.xif.paper.S936IndImageTransferActual
import tmp.sheaf.xif.paper.S931IndImageBoundedActual
import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S952IndImageSubsetOActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S931IndImageBoundedActual
open LeanFormal.IUT.XiFPaper.S936IndImageTransferActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : PaperIndImageData (l := l) T b)

/-- Exact geometric condition: the actual paper Ind image is contained in O_hol. -/
def S952IndImageSubsetO : Prop :=
  D.indImage ⊆ S922O (l := l) T b

theorem s952IndImageSubsetO_iff_bounded :
    S952IndImageSubsetO (l := l) T b D ↔
      S922IndImageBounded (l := l) T b D :=
  Iff.rfl

/-- Conditional actual O-containment from the S931/S922 condition. -/
theorem s952IndImageSubsetO_of_bounded
    (h : S922IndImageBounded (l := l) T b D) :
    S952IndImageSubsetO (l := l) T b D :=
  h

/-- Norm-one exact condition recorded by S936. -/
def S952IndImageNormLeOne : Prop :=
  ∀ x : qVFamTensorBlock T b, x ∈ D.indImage → ‖x‖ ≤ 1

/-- Exact missing data for the actual Ind image: nonempty, transfer fields, and
the O-bound.  No empty image and no theta-only substitution. -/
structure S952ActualIndImageBounded where
  D : (b : Bad (nativePlaceSelection T)) → PaperIndImageData (l := l) T b
  indImage_nonempty : ∀ b, (D b).indImage.Nonempty
  ind1_transfer : ∀ b, (D b).ind1_transfer
  ind2_transfer : ∀ b, (D b).ind2_transfer
  ind3_transfer : ∀ b, (D b).ind3_transfer
  bounded : ∀ b, S952IndImageSubsetO (l := l) T b (D b)

def S952ActualIndImageBoundedRequired : Prop :=
  Nonempty (S952ActualIndImageBounded (l := l) T)

end LeanFormal.IUT.XiFPaper.S952IndImageSubsetOActual

end
