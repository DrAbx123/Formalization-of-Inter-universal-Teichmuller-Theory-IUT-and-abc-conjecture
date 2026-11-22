import tmp.sheaf.xif.paper.S436KSideQVActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import tmp.sheaf.xif.paper.S467KrootOrderControlAuditActual
/-! # S605: qVFamilyK versus the paper K_v q_v spec
S438 constructs the actual K-side candidate qVFamilyK; S436 records the paper
KSideQVFamilySpec.  The place choice qVFamilyKLift is Classical.choose of comap
surjectivity, while the paper spec uses sectionFiniteLift; their equality, the
Tate uniformization, and the order formula are recorded as the minimal exact
gap.  The conditional spec construction is actual. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S605KSideQVActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S467KrootOrderControlAuditActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Minimal comparison data for qVFamilyK = paper K_v q_v. -/
structure KSideQVComparisonData where
  place_eq : qVFamilyKLift T b = kSidePlace (T := T) b
  shadow_eq : fkDescentShadow (nativePlaceSelection T) b.1 =
    (nativeBadLift T).lift b
  qSection : FinitePlaceQCandidate (kSidePlace (T := T) b)
  qSection_eq : qSection = place_eq.symm ▸ qVFamilyK T b
  uniformization : TateCurveComparison (kSideCurve (T := T))
    (kSidePlace (T := T) b) qSection
  order_eq : qSection.order =
    fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 *
      (qVFamily T b).order
/-- Exact minimal gap for identifying qVFamilyK with the paper K-side q_v. -/
def KSideQVComparisonRequired : Prop :=
  Nonempty (KSideQVComparisonData (T := T) (b := b))
/-- Actual conditional KSideQVFamilySpec from the minimal comparison data. -/
noncomputable def kSideQVFamilySpecOfComparison
    (G : KSideQVComparisonData (T := T) (b := b)) :
    KSideQVFamilySpec (T := T) (b := b) where
  kPlace := kSidePlace (T := T) b
  kPlace_eq := rfl
  kCurve := kSideCurve (T := T)
  kCurve_eq := rfl
  q := G.qSection
  uniformization := G.uniformization
  fPlace := (nativeBadLift T).lift b
  fPlace_eq := rfl
  shadow_compatible := G.shadow_eq
  fOrder := (qVFamily T b).order
  fOrder_eq := rfl
  order_eq := G.order_eq
/-- Conditional existence of the paper K-side q_v object. -/
theorem kSideQVFamilyRequired_of_comparison
    (G : KSideQVComparisonData (T := T) (b := b)) :
    KSideQVFamilyRequired (T := T) (b := b) :=
  ⟨kSideQVFamilySpecOfComparison (T := T) (b := b) G⟩
/-- Exact minimal gap package, kept separate from the conditional spec. -/
def KSideQVExactGap : Prop :=
  KSideQVComparisonRequired (T := T) (b := b)
end LeanFormal.IUT.XiFPaper.S605KSideQVActual
