import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
import tmp.sheaf.xif.PaperSignedHull

/-! # S1134: audit — multiradial S vs concrete PaperSignedHull

Correction: in Mochizuki LVEx, S is the multiradial hull
  closure(theta images ∪ Ind1/2/3 images),
not the concrete PaperSignedHull procession average.

Existing actual files:
* S916PaperMultiradialSActual:
    paperSImageUnion D = paperRootThetaImageNZ ∪ D.indImage
    paperSHull D = closure (paperSImageUnion D)
  and modelHull ⊆ paperSHull using only the theta branch.
* tmp.sheaf.xif.PaperSignedHull:
    PaperSignedHull.ambient.hull is the canonical arithmetic hull;
    signedHullLogVolume = -procession.average is the concrete signed scalar.
  Its hnormal field identifies the ambient hull log-volume with
  ENNReal.ofReal procession.average, not with the multiradial image hull.

Thus the concrete PaperSignedHull and the multiradial S are different
objects.  The tree supplies no actual equality
  P.ambient.hull = paperSHull D
and no actual identification of the concrete signed average with the
multiradial hull log.  This file records the actual multiradial containments
and the exact remaining bridge; it does not use the concrete theta average as S.

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1134PaperScalarAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open MeasureTheory Topology

universe u uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (D : PaperIndImageData (l := l) T b)

/-- Actual: multiradial image union is theta image union with the Ind image. -/
theorem s1134PaperSImageUnion_eq :
    paperSImageUnion (l := l) T b D =
      paperRootThetaImageNZ (l := l) T b ∪ D.indImage := rfl

/-- Actual: multiradial S is the closure of that union. -/
theorem s1134PaperSHull_eq :
    paperSHull (l := l) T b D =
      closure (paperRootThetaImageNZ (l := l) T b ∪ D.indImage) := rfl

/-- Actual: the model hull is contained in the multiradial hull, via theta. -/
theorem s1134ModelHull_subset_paperSHull :
    modelHull (l := l) T b ⊆ paperSHull (l := l) T b D :=
  modelHull_subset_paperSHull (l := l) T b D

/-- Exact: concrete PaperSignedHull ambient hull equals the multiradial S. -/
def S1134ConcreteHullEqMultiradial : Prop :=
  P.ambient.hull = paperSHull (l := l) T b D

/-- Exact: concrete signed scalar equals the multiradial hull log (toReal). -/
def S1134ConcreteAverageEqMultiradialHullLog : Prop :=
  P.signedHullLogVolume = -(P.ambient.logVolume (paperSHull (l := l) T b D)).toReal

/-- Exact: the Ind image transfer datum needed for a true multiradial S. -/
def S1134IndImageTransferRequired : Prop :=
  Nonempty (S936IndImageTransferData (l := l) T b)

/-- Exact strict enlargement of the multiradial hull. -/
def S1134PaperSStrictEnlargement : Prop :=
  PaperSStrictEnlargement (l := l) T b D

end LeanFormal.IUT.XiFPaper.S1134PaperScalarAuditActual

end
