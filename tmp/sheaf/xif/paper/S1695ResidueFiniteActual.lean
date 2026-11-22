import tmp.sheaf.xif.paper.S1694ResidueUnitRootActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
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
open LeanFormal.IUT.XiFPaper.S1681UnitRootKummerActual
open LeanFormal.IUT.XiFPaper.S1682PrincipalUnitPowerActual
open LeanFormal.IUT.XiFPaper.S1694ResidueUnitRootActual
namespace LeanFormal.IUT.XiFPaper.S1695ResidueFiniteActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
noncomputable instance s1695ResidueFieldFinite :
    Finite (IsLocalRing.ResidueField (O T b)) := by
  change Finite (IsLocalRing.ResidueField (A T b))
  change Finite (IsLocalRing.ResidueField
    ((sectionKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
  exact Finite.of_equiv _ (residueEquivAdicCompletionIntegers
    (K := T.arithmetic.K) (sectionKPlace T b)).toEquiv
theorem s1695ResidueRoot_iff_pow :
    S1682ResidueUnitTwoLRootRequired (l := l) T b ↔
      s1694ResidueUnit T b ^
        (Nat.card (IsLocalRing.ResidueField (O T b))ˣ /
          (Nat.card (IsLocalRing.ResidueField (O T b))ˣ).gcd
            (2 * l.value)) = 1 :=
  @s1694ResidueRoot_iff_pow_card_div_gcd (l := l) T b
    (s1695ResidueFieldFinite T b)
theorem s1695NoResidueRoot_of_pow_ne_one
    (h : s1694ResidueUnit T b ^
      (Nat.card (IsLocalRing.ResidueField (O T b))ˣ /
        (Nat.card (IsLocalRing.ResidueField (O T b))ˣ).gcd
          (2 * l.value)) ≠ 1) :
    ¬ S1682ResidueUnitTwoLRootRequired (l := l) T b := by
  intro hr
  exact h ((s1695ResidueRoot_iff_pow (l := l) T b).mp hr)
theorem s1695ResidueRoot_of_pow_eq_one
    (h : s1694ResidueUnit T b ^
      (Nat.card (IsLocalRing.ResidueField (O T b))ˣ /
        (Nat.card (IsLocalRing.ResidueField (O T b))ˣ).gcd
          (2 * l.value)) = 1) :
    S1682ResidueUnitTwoLRootRequired (l := l) T b :=
  (s1695ResidueRoot_iff_pow (l := l) T b).mpr h
theorem s1695CardUnits :
    Nat.card (IsLocalRing.ResidueField (O T b))ˣ =
      Nat.card (IsLocalRing.ResidueField (O T b)) - 1 :=
  Nat.card_units _
theorem s1695ResidueRoot_of_gcd_eq_one
    (hg : (Nat.card (IsLocalRing.ResidueField (O T b)) - 1).gcd
      (2 * l.value) = 1) :
    S1682ResidueUnitTwoLRootRequired (l := l) T b := by
  rw [s1695ResidueRoot_iff_pow]
  rw [s1695CardUnits, hg, Nat.div_one]
  rw [← s1695CardUnits]
  exact pow_card_eq_one' (G := (IsLocalRing.ResidueField (O T b))ˣ)
    (x := s1694ResidueUnit T b)
theorem s1695ResidueRoot_iff_pow_card_sub_one :
    S1682ResidueUnitTwoLRootRequired (l := l) T b ↔
      s1694ResidueUnit T b ^
        ((Nat.card (IsLocalRing.ResidueField (O T b)) - 1) /
          (Nat.card (IsLocalRing.ResidueField (O T b)) - 1).gcd
            (2 * l.value)) = 1 := by
  rw [s1695ResidueRoot_iff_pow, s1695CardUnits]
theorem s1695UnitRoot_of_gcd_eq_one
    (hg : (Nat.card (IsLocalRing.ResidueField (O T b)) - 1).gcd
      (2 * l.value) = 1)
    (hcop : Nat.Coprime (2 * l.value)
      (residueCharacteristic (sectionKPlace T b))) :
    S1677UnitRootRequired (l := l) T b :=
  s1682S1677UnitRootRequired_of_residueRoot (T := T) (b := b) hcop
    (s1695ResidueRoot_of_gcd_eq_one (l := l) T b hg)
end LeanFormal.IUT.XiFPaper.S1695ResidueFiniteActual


end
