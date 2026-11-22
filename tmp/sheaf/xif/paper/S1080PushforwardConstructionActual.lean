import tmp.sheaf.xif.paper.S1079RootStackMeasureAuditActual
import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual
import tmp.sheaf.xif.paper.S1076RootStackPaperThetaHullMeasureActual

/-! # S1080: pushforward (L-stalk) measure on the root-stack hull

s1079HaarOnRange is the pushforward of the qVFam-block additive Haar along
rootStackEmbedding.  Its value on the hull reduces to the domain Haar of
paperLambdaORegion.  Positivity and finiteness are therefore domain-lattice
statements; they are not ambient rootStackHaar statements.

S824's stacky measure is the ambient L(mu)-Haar, invariant under the mu action.
The pushforward from L is supported on the proper L-stalk and is not the
ambient Haar; equality would be an exact measure identity, recorded as
S1080EqS824StackyMeasure.  No ambient positivity is asserted. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1076RootStackPaperThetaHullMeasureActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Constructed L-stalk pushforward measure. -/
noncomputable def s1080PushforwardHaar : Measure (rootStackExtension T b) :=
  s1079HaarOnRange (l := l) T b

/-- Exact pushforward identity on the image hull: the pushforward measure of the
image equals the domain Haar of the lambda-O region. -/
def S1080PushforwardHullEq : Prop :=
  s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) =
    (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily (l := l) T b))

/-- Domain-lattice positivity (the correct positivity statement). -/
def S1080DomainPositivity : Prop :=
  0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
    (paperLambdaORegion (l := l) T b
      (paperRootCoefficientFamily (l := l) T b))

/-- Domain-lattice finiteness. -/
def S1080DomainFiniteness : Prop :=
  (Measure.addHaar : Measure (qVFamTensorBlock T b))
    (paperLambdaORegion (l := l) T b
      (paperRootCoefficientFamily (l := l) T b)) < ⊤

/-- Hull positivity for the constructed pushforward measure, from the exact
pushforward identity and domain positivity. -/
theorem s1080Hull_positivity_of_domain
    (heq : S1080PushforwardHullEq (l := l) T b)
    (hpos : S1080DomainPositivity (l := l) T b) :
    0 < s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) := by
  rw [heq]
  exact hpos

/-- Hull finiteness for the constructed pushforward measure. -/
theorem s1080Hull_finiteness_of_domain
    (heq : S1080PushforwardHullEq (l := l) T b)
    (hfin : S1080DomainFiniteness (l := l) T b) :
    s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤ := by
  rw [heq]
  exact hfin

/-- Exact equality with S824's ambient stacky Haar. -/
def S1080EqS824StackyMeasure : Prop :=
  s1080PushforwardHaar (l := l) T b = rootStackHaar (l := l) T b

/-- Exact obstruction: the ambient Haar of the proper embedding range is zero,
while the pushforward is supported there. -/
def S1080AmbientZeroOnRange : Prop :=
  rootStackHaar (l := l) T b
    (Set.range (rootStackEmbedding (l := l) T b)) = 0

/-- Exact minimum: pushforward identity + domain positivity/finiteness. -/
def S1080ExactMinimum : Prop :=
  S1080PushforwardHullEq (l := l) T b ∧
    S1080DomainPositivity (l := l) T b ∧
      S1080DomainFiniteness (l := l) T b

end LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual

end
