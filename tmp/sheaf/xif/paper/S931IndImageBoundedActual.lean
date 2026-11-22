/-! IMPORTANT (user directive): emptyPaperIndImageData below is only an
internal lower-bound sanity check.  It is NOT the paper Ind image and must
never be used as a final paper S.  The paper target keeps paperSHull D with
the actual Ind image; if that image is missing, the exact gap is recorded,
not removed. -/

import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual
import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S931IndImageBoundedActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : PaperIndImageData (l := l) T b)

theorem indImageBounded_iff :
    S922IndImageBounded (l := l) T b D ↔
      D.indImage ⊆ S922O (l := l) T b :=
  Iff.rfl

/-- Exact minimal side condition left by S929/S931. -/
def S931IndImageBoundGap : Prop :=
  D.indImage ⊆ S922O (l := l) T b

/-- INTERNAL ONLY lower-bound instance. This is not the paper Ind image and is
not a final paper-S theorem. -/
def emptyPaperIndImageData (p1 p2 p3 : Prop) : PaperIndImageData (l := l) T b where
  indImage := ∅
  ind1_transfer := p1
  ind2_transfer := p2
  ind3_transfer := p3

theorem emptyIndImage_bounded (p1 p2 p3 : Prop) :
    S922IndImageBounded (l := l) T b (emptyPaperIndImageData (l := l) T b p1 p2 p3) := by
  intro x hx
  exact False.elim hx

/-- If the supplied Ind image is exactly the canonical unit region O, the
boundedness condition is immediate. -/
theorem indImageBounded_of_eq_O (h : D.indImage = S922O (l := l) T b) :
    S922IndImageBounded (l := l) T b D := by
  rw [indImageBounded_iff, h]

/-- Exact missing object: a transfer of the Ind1/Ind2/Ind3 tensor-packet images
into the qVFam tensor block, together with the containment in O. -/
structure IndImageTransferToBlock where
  blockImage : Set (qVFamTensorBlock T b)
  blockImage_eq : blockImage = D.indImage
  blockImage_subset_O : blockImage ⊆ S922O (l := l) T b

def IndImageTransferToBlockRequired : Prop :=
  Nonempty (IndImageTransferToBlock (l := l) T b D)

end LeanFormal.IUT.XiFPaper.S931IndImageBoundedActual
end