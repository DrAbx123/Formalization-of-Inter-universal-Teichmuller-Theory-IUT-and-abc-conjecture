import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open MeasureTheory

universe u ua uv upi umon ui uR uVQ
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing Ind-image transfer data.  The Ind1/Ind2/Ind3 actions live
on tensor packets/x-mu stages; their images in the qVFam tensor block are not
supplied by the current tree.  This records only the needed image set and the
exact transfer propositions; no image equality is asserted. -/
structure PaperIndImageData where
  indImage : Set (qVFamTensorBlock T b)
  ind1_transfer : Prop
  ind2_transfer : Prop
  ind3_transfer : Prop

/-- Theta possible-image union plus the supplied Ind image set. -/
noncomputable def paperSImageUnion (D : PaperIndImageData (l := l) T b) :
    Set (qVFamTensorBlock T b) :=
  paperRootThetaImageNZ (l := l) T b ∪ D.indImage

/-- The paper multiradial closure hull S. -/
noncomputable def paperSHull (D : PaperIndImageData (l := l) T b) :
    Set (qVFamTensorBlock T b) :=
  closure (paperSImageUnion (l := l) T b D)

/-- Actual containment: the model hull R is contained in S, using only the
theta image part.  No equality is asserted. -/
theorem modelHull_subset_paperSHull
    (D : PaperIndImageData (l := l) T b) :
    modelHull T b ⊆ paperSHull (l := l) T b D := by
  intro x hx
  unfold modelHull at hx
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b] at hx
  apply subset_closure
  left
  apply Set.mem_iUnion.mpr
  refine ⟨⟨oneLabel l, paperOneLabel_ne_zero (l := l)⟩, ?_⟩
  change x ∈ paperLambdaORegion (l := l) T b
    (fun i => ((gaussExponent (oneLabel l).1).toNat : Real) *
      paperRootCoefficientFamily T b i)
  simpa [gaussExponent_oneLabel] using hx

/-- Strict enlargement is the exact condition that the supplied Ind image has
a point outside the model hull.  No point is fabricated. -/
def PaperSStrictEnlargement (D : PaperIndImageData (l := l) T b) : Prop :=
  ∃ x : qVFamTensorBlock T b, x ∈ D.indImage ∧ x ∉ modelHull T b

/-- Strict enlargement gives a proper containment R ⊂ S. -/
theorem modelHull_ssubset_paperSHull_of_strict
    (D : PaperIndImageData (l := l) T b)
    (hstrict : PaperSStrictEnlargement (l := l) T b D) :
    modelHull T b ⊂ paperSHull (l := l) T b D := by
  refine ⟨modelHull_subset_paperSHull (l := l) T b D, ?_⟩
  rintro hsub
  rcases hstrict with ⟨x, hxind, hxnot⟩
  exact hxnot (hsub (subset_closure (Or.inr hxind)))

/-- Exact missing Ind-image transfer obligations, as a single Prop. -/
def PaperIndImageTransferRequired (D : PaperIndImageData (l := l) T b) : Prop :=
  D.ind1_transfer ∧ D.ind2_transfer ∧ D.ind3_transfer

end LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual

end
