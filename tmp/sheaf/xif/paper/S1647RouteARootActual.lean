import tmp.sheaf.xif.paper.S1444ReportAKPlaceQActual
import Mathlib.FieldTheory.IsAlgClosed.Basic
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S605KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
namespace LeanFormal.IUT.XiFPaper.S1647RouteARootActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
abbrev Kv : Type _ := Completion (sectionKPlace T b)
abbrev Lv : Type _ := AlgebraicClosure (Kv T b)
def s1647n2l : Nat := 2 * l.value
theorem s1647n2l_pos : 0 < s1647n2l (l := l) := by
  unfold s1647n2l
  exact Nat.mul_pos (by norm_num) l.prime.pos
theorem s1647SectionKPlace_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b) =
      sectionFPlace T b := sectionKPlace_comap T b
theorem s1647SectionQ_q :
    (sectionQ T b).q =
      completionMap (k := T.arithmetic.F) (sectionKPlace T b) (sectionFQ T b).q :=
  sectionQ_q T b
theorem s1647SectionQ_order :
    (sectionQ T b).order =
      ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F)
        (sectionKPlace T b) * (sectionFQ T b).order := sectionQ_order T b
theorem s1647SectionQ_norm :
    ‖(sectionQ T b).q‖ =
      ‖(sectionFQ T b).q‖ ^
        ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F)
          (sectionKPlace T b) := sectionQ_norm T b
def S1647S605FirstField : Prop := KSideQVFirstField (T := T) (b := b)
theorem s1647FirstField_of_comparisonData
    (G : KSideQVComparisonData (T := T) (b := b)) :
      S1647S605FirstField (T := T) (b := b) := G.place_eq
def SectionKPlaceTwoLRootRequired : Prop := SectionKPlaceTwoLRoot (T := T) (b := b)
theorem s1647Root_order_necessary :
    SectionKPlaceTwoLRootRequired (T := T) (b := b) →
      (2 * l.value) ∣ (sectionQ T b).order := by
  intro h
  exact sectionQ_twoLRoot_twoL_dvd_order (T := T) (b := b) h.some
theorem s1647Root_l_dvd_ramification :
    SectionKPlaceTwoLRootRequired (T := T) (b := b) →
      l.value ∣ fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 := by
  intro h
  exact sectionQ_twoLRoot_l_dvd_ramification (T := T) (b := b) h.some
noncomputable def s1647ACRoot : Lv T b :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (Kv T b) (Lv T b) (sectionQ T b).q) (s1647n2l_pos (l := l)))
theorem s1647ACRoot_pow :
    s1647ACRoot (T := T) (b := b) ^ s1647n2l (l := l) =
      algebraMap (Kv T b) (Lv T b) (sectionQ T b).q := by
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (Kv T b) (Lv T b) (sectionQ T b).q) (s1647n2l_pos (l := l)))
def S1647RootDescentGap : Prop :=
  (SectionKPlaceTwoLRootRequired (T := T) (b := b) →
      (2 * l.value) ∣ (sectionQ T b).order) ∧
    ∃ r : Lv T b, r ^ s1647n2l (l := l) =
      algebraMap (Kv T b) (Lv T b) (sectionQ T b).q
theorem s1647RootDescentGap_holds : S1647RootDescentGap (T := T) (b := b) :=
  ⟨s1647Root_order_necessary (T := T) (b := b),
    ⟨s1647ACRoot (T := T) (b := b), s1647ACRoot_pow (T := T) (b := b)⟩⟩
def S1647RootInCompletionRemaining : Prop :=
  SectionKPlaceTwoLRootRequired (T := T) (b := b)
#check S1647S605FirstField
#check s1647FirstField_of_comparisonData
#check SectionKPlaceTwoLRootRequired
#check s1647Root_order_necessary
#check s1647Root_l_dvd_ramification
#check s1647ACRoot_pow
#check s1647RootDescentGap_holds
#check S1647RootInCompletionRemaining
end LeanFormal.IUT.XiFPaper.S1647RouteARootActual
end
