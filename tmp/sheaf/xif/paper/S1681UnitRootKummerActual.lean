import tmp.sheaf.xif.paper.S1677UnitKummerActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1647RouteARootActual
open LeanFormal.IUT.XiFPaper.S1660SectionKPlaceRootActual
open LeanFormal.IUT.XiFPaper.S1668UnitRootDescentActual
open LeanFormal.IUT.XiFPaper.S1677UnitKummerActual
namespace LeanFormal.IUT.XiFPaper.S1681UnitRootKummerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
def S1681UnitRootLemma : Prop := S1677UnitRootRequired (l := l) T b
def S1681PrincipalUnitPowerSurjective : Prop :=
  ∀ u : (Ksection T b)ˣ,
    (Valued.v ((u : Ksection T b) - 1) :
      WithZero (Multiplicative Int)) < 1 →
    ∃ v : (Ksection T b)ˣ, v ^ (2 * l.value) = u
theorem s1681SectionKPlaceTwoLRoot_of_unitRoot
    (h : (2 * (l.value : ℤ)) ∣ ((sectionQ T b).order : ℤ))
    (v : (Ksection T b)ˣ)
    (hv : v ^ (2 * l.value) = s1668QUnitPartField T b) :
    SectionKPlaceTwoLRootRequired (T := T) (b := b) :=
  s1677SectionKPlaceTwoLRoot_of_unitRoot (l := l) T b h v hv
#check S1681UnitRootLemma
#check S1681PrincipalUnitPowerSurjective
#check s1681SectionKPlaceTwoLRoot_of_unitRoot
end LeanFormal.IUT.XiFPaper.S1681UnitRootKummerActual
end
