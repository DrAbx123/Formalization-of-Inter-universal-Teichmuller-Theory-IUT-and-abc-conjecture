import tmp.sheaf.xif.paper.S753StructuralContainmentActual
import tmp.sheaf.xif.paper.S746OrdinaryOTriActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
/-! # S777: paper q[2u] target needs the root-stack carrier
S753 gives actual structural containment and the paper q[2u] log
-(order/(2l)) log p.  S746 proves the ordinary O^tri has no 2l-root of an
exponent prime to l.  Therefore the paper target is the root-stack carrier
plus the /(2l) qPilot scalar; this file records the exact carrier datum. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S777PaperTargetRootStackAlignmentActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S753StructuralContainmentActual
open LeanFormal.IUT.XiFPaper.S746OrdinaryOTriActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]
/-- Actual paper q[2u] scalar from S753. -/
theorem s777_paperQLog_eq :
    paperQLog (l := l) T b =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) :=
  rfl
/-- Actual structural containment of S753. -/
theorem s777_structuralContainment :
    qPilotNormRegion (l := l) T b ⊆ rootNormHull (l := l) T b :=
  qPilotNormRegion_subset_rootNormHull (l := l) T b
/-- Ordinary O^tri cannot carry the 2l-root. -/
theorem s777_ordinary_no_root
    {K : Type u} [Monoid K] (u : Kˣ) (n : Nat)
    (h : ¬ l.value ∣ n) :
    ¬ ∃ r : OrdinaryOTri K,
      OrdinaryOTri.pow r (2 * l.value) = OrdinaryOTri.ofExponent u n :=
  ordinaryOTri_no_q2u_root (l := l) u n h
/-- Exact paper carrier datum: a root-stack O^tri whose ordinary part is the
q[1u] element and which carries the extra root.  No inhabitant is asserted. -/
structure PaperRootStackCarrier
    {K : Type u} [Monoid K] (u : Kˣ) (n : Nat) where
  rootStack : RootStackOTri K
  ordinary_eq : rootStack.ordinary = OrdinaryOTri.ofExponent u n
  has_root : rootStack.root
/-- Exact remaining paper-target datum. -/
def PaperRootStackCarrierRequired
    {K : Type u} [Monoid K] (u : Kˣ) (n : Nat) : Prop :=
  Nonempty (PaperRootStackCarrier u n)
/-- The paper q[2u] scalar is the root-stack normalization, not an ordinary
O^tri element; this records the exact alignment requirement. -/
def PaperTargetNeedsRootStack : Prop :=
  (∀ (K : Type u) [Monoid K] (u : Kˣ) (n : Nat), ¬ l.value ∣ n →
    ¬ ∃ r : OrdinaryOTri K,
      OrdinaryOTri.pow r (2 * l.value) = OrdinaryOTri.ofExponent u n) ∧
  (paperQLog (l := l) T b =
    -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
      Real.log (qVFamTensorP T b : Real)))
/-- The actual alignment theorem. -/
theorem paperTargetNeedsRootStack_actual :
    PaperTargetNeedsRootStack (l := l) T b := by
  constructor
  · intro K _ u n h
    exact ordinaryOTri_no_q2u_root (l := l) u n h
  · rfl
end LeanFormal.IUT.XiFPaper.S777PaperTargetRootStackAlignmentActual
