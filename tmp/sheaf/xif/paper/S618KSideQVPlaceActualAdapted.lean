import tmp.sheaf.xif.paper.S605KSideQVActual
import tmp.sheaf.xif.paper.S436KSideQVActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import tmp.sheaf.xif.paper.S467KrootOrderControlAuditActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S618KSideQVPlaceActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S605KSideQVActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S467KrootOrderControlAuditActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The qVFamilyKLift and the section lift lie over the same F-place; hence
place equality forces the shadow equality. -/
theorem place_eq_imp_shadow_eq
    (hplace : qVFamilyKLift T b = kSidePlace (T := T) b) :
    fkDescentShadow (nativePlaceSelection T) b.1 =
      (nativeBadLift T).lift b := by
  change NumberFieldFinitePlace.comap (k := T.arithmetic.F)
      (sectionFiniteLift (nativePlaceSelection T) b.1) =
    (nativeBadLift T).lift b
  rw [← hplace]
  exact qVFamilyKLift_comap T b

/-- Exact place/shadow gap: the two Classical choices have different
definitions and the shadow equality is not obtained from the section
definition alone. -/
structure KSideQVPlaceGap where
  place_eq : qVFamilyKLift T b = kSidePlace (T := T) b
  shadow_eq : fkDescentShadow (nativePlaceSelection T) b.1 =
    (nativeBadLift T).lift b

def KSideQVPlaceGapRequired : Prop :=
  Nonempty (KSideQVPlaceGap (T := T) (b := b))

/-- Conditional S605 comparison data from exact place/shadow data and the
remaining explicit fields. -/
noncomputable def kSideQVComparisonDataOfPlace
    (hplace : qVFamilyKLift T b = kSidePlace (T := T) b)
    (qSection : FinitePlaceQCandidate (kSidePlace (T := T) b))
    (hqSection : qSection = hplace.symm ▸ qVFamilyK T b)
    (uniformization : TateCurveComparison (kSideCurve (T := T))
      (kSidePlace (T := T) b) qSection)
    (order_eq : qSection.order =
      fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 *
        (qVFamily T b).order) :
    KSideQVComparisonData (T := T) (b := b) where
  place_eq := hplace
  shadow_eq := place_eq_imp_shadow_eq (T := T) (b := b) hplace
  qSection := qSection
  qSection_eq := hqSection
  uniformization := uniformization
  order_eq := order_eq

end LeanFormal.IUT.XiFPaper.S618KSideQVPlaceActualAdapted

end
