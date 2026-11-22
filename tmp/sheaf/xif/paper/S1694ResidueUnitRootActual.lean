import tmp.sheaf.xif.paper.S1682PrincipalUnitPowerActual
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
namespace LeanFormal.IUT.XiFPaper.S1694ResidueUnitRootActual
theorem s1694RangePowEqKer (G : Type*) [CommGroup G] [IsCyclic G] [Finite G]
    (n : Nat) :
    (powMonoidHom n : G →* G).range =
      (powMonoidHom (Nat.card G / (Nat.card G).gcd n) : G →* G).ker := by
  classical
  let m := Nat.card G
  let g := m.gcd n
  let d := m / g
  have hmpos : 0 < m := Nat.card_pos
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n hmpos
  have hgm : g ∣ m := Nat.gcd_dvd_left m n
  have hgn : g ∣ n := Nat.gcd_dvd_right m n
  have hle : (powMonoidHom n : G →* G).range ≤
      (powMonoidHom d : G →* G).ker := by
    rintro y ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have hdiv : m ∣ n * d := by
      obtain ⟨m', hm'⟩ := hgm
      obtain ⟨n', hn'⟩ := hgn
      have hd : d = m' := by
        show m / g = m'
        rw [hm']
        exact Nat.mul_div_cancel_left m' hgpos
      refine ⟨n', ?_⟩
      rw [hd, hn', hm']
      ring
    obtain ⟨k, hk⟩ := hdiv
    change (x ^ n) ^ d = 1
    rw [← pow_mul, hk, pow_mul, pow_card_eq_one']
    simp
  have hrange : Nat.card (powMonoidHom n : G →* G).range = d := by
    rw [IsCyclic.card_powMonoidHom_range (G := G) n]
  have hker : Nat.card (powMonoidHom d : G →* G).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker (G := G) d]
    exact Nat.gcd_eq_right (Nat.div_dvd_of_dvd hgm)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hker, hrange])
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
noncomputable def s1694ResidueUnit :
    (IsLocalRing.ResidueField (O T b))ˣ :=
  Units.map (IsLocalRing.residue (O T b)).toMonoidHom (s1682QUnitPartO T b)
theorem s1694ResidueRoot_iff_pow_card_div_gcd
    [Finite (IsLocalRing.ResidueField (O T b))] :
    S1682ResidueUnitTwoLRootRequired (l := l) T b ↔
      s1694ResidueUnit T b ^
        (Nat.card (IsLocalRing.ResidueField (O T b))ˣ /
        (Nat.card (IsLocalRing.ResidueField (O T b))ˣ).gcd (2 * l.value)) = 1 := by
  let n := 2 * l.value
  let d := Nat.card (IsLocalRing.ResidueField (O T b))ˣ /
    (Nat.card (IsLocalRing.ResidueField (O T b))ˣ).gcd n
  haveI : Finite (IsLocalRing.ResidueField (O T b))ˣ := inferInstance
  haveI : IsCyclic (IsLocalRing.ResidueField (O T b))ˣ := inferInstance
  have hpow := s1694RangePowEqKer (G := (IsLocalRing.ResidueField (O T b))ˣ) n
  constructor
  · rintro ⟨β, hβ⟩
    have hm : s1694ResidueUnit T b ∈
        (powMonoidHom n : (IsLocalRing.ResidueField (O T b))ˣ →*
      (IsLocalRing.ResidueField (O T b))ˣ).range := ⟨β, hβ⟩
    rw [hpow] at hm
    simpa [MonoidHom.mem_ker, powMonoidHom_apply, d, n] using hm
  · intro h
    have hm : s1694ResidueUnit T b ∈
        (powMonoidHom d : (IsLocalRing.ResidueField (O T b))ˣ →*
      (IsLocalRing.ResidueField (O T b))ˣ).ker := by
      simpa [MonoidHom.mem_ker, powMonoidHom_apply, d, n] using h
    rw [← hpow] at hm
    exact hm
theorem s1694ResidueRoot_false_of_pow_ne_one
    [Finite (IsLocalRing.ResidueField (O T b))]
    (h : s1694ResidueUnit T b ^
      (Nat.card (IsLocalRing.ResidueField (O T b))ˣ /
      (Nat.card (IsLocalRing.ResidueField (O T b))ˣ).gcd (2 * l.value)) ≠ 1) :
    ¬ S1682ResidueUnitTwoLRootRequired (l := l) T b :=
  fun hroot => h ((s1694ResidueRoot_iff_pow_card_div_gcd (l := l) T b).mp hroot)
end LeanFormal.IUT.XiFPaper.S1694ResidueUnitRootActual

end
