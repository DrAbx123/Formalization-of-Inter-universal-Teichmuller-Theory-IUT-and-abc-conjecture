import tmp.sheaf.xif.paper.S2223TateBridgeActual

/-!
# S2296: the base-unit descent of the K-side Tate torsion classes

## What this file proves

S2223 reduced the two paper source conditions

* `S2190QSquareSource`: `q_v` is a square in the completion at the section K-place,
* `S2190QLthPowerSource`: `q_v` is an `l`-th power in that completion,

to the existence, for a K-side Tate torsion point `P`, of a *base unit*
`x` in the units of the completion with

`pointEquiv (mk x) = ofAdd P` and `x ^ n = q_v ^ m`

together with a parity (`n = 2`) or coprimality (`n = l`) condition on `m`.

This file proves the descent itself:

* `tateDescent`: if `P` is a Galois-fixed `n`-torsion point of the K-side
  Tate point group, then the class `pointEquiv⁻¹ P` has a representative in
  the units of the completion `K_v`, and its `n`-th power is an integral
  power of `q_v`.

The proof is the paper argument, with no group cohomology: lift the class to
`y ∈ (LK)ˣ`.  Since `n • P = 0`, the unit `y ^ n` lies in the Tate
subgroup `q_v ^ ℤ`, say `y ^ n = q_v ^ m`.  Galois fixedness of `P` gives
`σ y / y ∈ q_v ^ ℤ` for every `σ`, while `(σ y / y) ^ n = σ(y^n)/y^n = 1`
because `q_v` is fixed by `σ`.  Hence `σ y / y ∈ q_v ^ ℤ ∩ μ_n`, and
`q_v` is not a root of unity (it has valuation `< 1`), so `σ y / y = 1`.
Thus `y` is fixed by the whole absolute Galois group of `K_v`, hence lies in
`K_v`.

## Parity and coprimality

The exponent `m` is not arbitrary:

* `twoTorsion_of_even_exponent`: if `2 ∣ m` then `P` is either `0` or the
  single point represented by `-1`.  Hence three distinct nonzero Galois-fixed
  2-torsion points cannot all have even exponent
  (`three_twoTorsion_odd_exponent`), which gives the square source condition
  (`S2190QSquareSource_of_three_twoTorsion`).
* `lTorsion_class_eq_rootOfUnity`: if `l ∣ m` then `P` is the class of an
  `l`-th root of unity in `K_v`; the field `K_v` has at most `l` such roots,
  so a family of `l + 1` distinct Galois-fixed `l`-torsion points must contain
  one whose exponent is prime to `l` (`exists_coprime_of_card_gt`).

## The exact first missing

The uniformization comparison supplies no map from the algebraic closure of the
F-side completion to that of the K-side completion at the level of points, and
clause (c)'s rational torsion lives on the F-side.  The geometric input
"three distinct nonzero Galois-fixed 2-torsion points of `SideKPoint T b`"
(`S2296ThreeRationalTwoTorsion`) is therefore isolated as the exact remaining
gap; `S2190TwoTorsionToQSqrtBridge_of_threeRationalTwoTorsion` shows the
clause-(c) bridge of S2190 follows from it.  The analogous `l`-torsion input is
`S2296LRationalTorsionClass`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2296TateBaseUnitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2223TateBridgeActual
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual
open WeierstrassCurve

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The absolute Galois group of the completion `K_v` acting on the closure. -/
abbrev GalK : Type _ := LK T b ≃ₐ[Kv T b] LK T b

/-- The Tate parameter as a unit of the closure. -/
abbrev tateUnit : (LK T b)ˣ :=
  tateParameterUnit (sectionKPlace T b) (sectionQ T b).q (sectionQ T b).q_ne_zero

/-- The K-side Tate parameter in the completion. -/
abbrev tateQ : Completion (sectionKPlace T b) := (sectionQ T b).q

/-- The canonical map from the units of the completion to the units of the
algebraic closure. -/
abbrev unitsMap : (Kv T b)ˣ →* (LK T b)ˣ :=
  Units.map (algebraMap (Kv T b) (LK T b)).toMonoidHom

/-- The projective K-side curve over the closure. -/
abbrev WK : WeierstrassCurve.Projective (LK T b) := WKproj T b

/-! ## 1. `q_v` is not a root of unity -/

/-- No nonzero power of the completion q-parameter is one.  The proof uses the
strict valuation inequality of `FinitePlaceQCandidate`. -/
theorem tateQ_nat_pow_ne_one {n : Nat} (hn : n ≠ 0) : (tateQ T b) ^ n ≠ 1 := by
  intro h
  have hq : (tateQ T b) ≠ 0 := (sectionQ T b).q_ne_zero
  have hlt : (Valued.v (tateQ T b) : WithZero (Multiplicative Int)) < 1 :=
    (sectionQ T b).valuation_lt_one
  have hv : (Valued.v (tateQ T b) : WithZero (Multiplicative Int)) ^ n = 1 := by
    have h2 : (Valued.v ((tateQ T b) ^ n) : WithZero (Multiplicative Int)) = 1 := by
      rw [h, map_one]
    rwa [map_pow] at h2
  have hltn : (Valued.v (tateQ T b) : WithZero (Multiplicative Int)) ^ n < 1 :=
    pow_lt_one₀ bot_le hlt hn
  rw [hv] at hltn
  exact lt_irrefl 1 hltn

/-- The only integral power of the completion q-parameter equal to one is the
zeroth power. -/
theorem tateQ_zpow_eq_one {k : Int} (h : (tateQ T b) ^ k = 1) : k = 0 := by
  by_contra hk
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · have hzero_neg : (0 : Int) ≤ -k := by linarith
    have h3 : (tateQ T b) ^ (-k) = 1 := by
      rw [zpow_neg, h, inv_one]
    have h2 : (tateQ T b) ^ ((-k).toNat) = 1 := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hzero_neg]
      exact h3
    have hne : ((-k).toNat) ≠ 0 := by
      intro h0
      have hzero : (((-k).toNat : Nat) : Int) = 0 := by rw [h0]; rfl
      rw [Int.toNat_of_nonneg hzero_neg] at hzero
      linarith
    exact tateQ_nat_pow_ne_one T b hne h2
  · have hzero_pos : (0 : Int) ≤ k := by linarith
    have h2 : (tateQ T b) ^ k.toNat = 1 := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hzero_pos]
      exact h
    have hne : k.toNat ≠ 0 := by
      intro h0
      have hzero : ((k.toNat : Nat) : Int) = 0 := by rw [h0]; rfl
      rw [Int.toNat_of_nonneg hzero_pos] at hzero
      linarith
    exact tateQ_nat_pow_ne_one T b hne h2

/-- The Tate parameter unit has no nontrivial integral power equal to one. -/
theorem tateUnit_zpow_eq_one {k : Int} (h : (tateUnit T b) ^ k = 1) : k = 0 := by
  have hval : ((tateUnit T b ^ k : (LK T b)ˣ) : LK T b) = 1 := by
    rw [h, Units.val_one]
  have h2 : (algebraMap (Kv T b) (LK T b)) ((tateQ T b) ^ k) = 1 := by
    rw [map_zpow₀]
    rw [← hval, Units.val_zpow_eq_zpow_val]
    rfl
  exact tateQ_zpow_eq_one T b ((algebraMap (Kv T b) (LK T b)).injective h2)

/-- Coprimality form: the intersection `q_v ^ ℤ ∩ μ_n` is trivial. -/
theorem tateUnit_zpow_eq_one_of_pow_eq_one {k : Int} {n : Nat} (hn : 0 < n)
    (h : ((tateUnit T b) ^ k) ^ n = 1) : k = 0 := by
  have h2 : (tateUnit T b) ^ (k * (n : Int)) = 1 := by
    rw [zpow_mul, zpow_natCast]
    exact h
  have hkn : k * (n : Int) = 0 := tateUnit_zpow_eq_one T b h2
  rcases mul_eq_zero.mp hkn with h3 | h3
  · exact h3
  · have : (n : Int) ≠ 0 := by exact_mod_cast hn.ne'
    exact absurd h3 this


/-! ## 2. The base-unit descent -/

/-- A point of the K-side Tate point group is Galois fixed if every
K_v-automorphism of the closure fixes it. -/
def IsGaloisFixed (P : SideKPoint T b) : Prop :=
  forall σ : GalK T b, ((kSideCurve (T := T)).baseChange (Kv T b)).galoisActionOnPoint σ P = P

/-- **The base-unit descent.**  A Galois-fixed n-torsion point of the K-side
Tate point group has a representative in the units of the completion K_v, and
its n-th power is an integral power of the q-parameter.

This is the exact missing datum of S2223, proved here from the comparison and
Galois fixedness alone; the intersection of q_v ^ Z with the n-th roots of
unity is trivial because q_v is not a root of unity. -/
theorem tateDescent (P : SideKPoint T b) (n : Nat) (hn : 0 < n)
    (hfix : IsGaloisFixed T b P) (htors : n • P = 0) :
    ∃ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P ∧
        (x : Kv T b) ^ n = (tateQ T b) ^ m := by
  classical
  -- 1. lift the class to a unit of the closure
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective
    ((pointEquiv T b).symm (Multiplicative.ofAdd P))
  have hyP : pointEquiv T b (QuotientGroup.mk y) = Multiplicative.ofAdd P := by
    rw [hy, MulEquiv.apply_symm_apply]
  -- 2. the n-th power of the lift lies in the Tate subgroup
  have hker : QuotientGroup.mk (y ^ n) = (1 : DeckK T b) := by
    apply (pointEquiv T b).injective
    have h1 : pointEquiv T b (QuotientGroup.mk (y ^ n)) =
        (pointEquiv T b (QuotientGroup.mk y)) ^ n := by
      rw [QuotientGroup.mk_pow]
      exact map_pow (pointEquiv T b) _ n
    rw [h1, hyP, ← ofAdd_nsmul, htors, ofAdd_zero, map_one]
  have hmem : y ^ n ∈ Subgroup.zpowers (tateUnit T b) := by
    exact (QuotientGroup.eq_one_iff (y ^ n)).mp hker
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  -- hm : tateUnit ^ m = y ^ n
  -- 3. every Galois element fixes the class of the lift
  have hfix_class : ∀ σ : GalK T b,
      QuotientGroup.mk (Units.map σ.toRingEquiv.toMonoidHom y) = (QuotientGroup.mk y : DeckK T b) := by
    intro σ
    apply (pointEquiv T b).injective
    rw [pointEquiv_galois_naturality T b σ y, hyP]
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd P) = P from rfl]
    exact congrArg Multiplicative.ofAdd (hfix σ)
  -- 4. hence the quotient σ y / y lies in the Tate subgroup
  have hσdiv : ∀ σ : GalK T b, ∃ j : Int,
      Units.map σ.toRingEquiv.toMonoidHom y / y = (tateUnit T b) ^ j := by
    intro σ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      (QuotientGroup.eq_iff_div_mem.mp (hfix_class σ))
    exact ⟨j, hj.symm⟩
  -- 5. and σ y / y is an n-th root of unity
  have hσpow : ∀ σ : GalK T b,
      (Units.map σ.toRingEquiv.toMonoidHom y / y) ^ n = 1 := by
    intro σ
    have h1 : (Units.map σ.toRingEquiv.toMonoidHom y) ^ n = y ^ n := by
      calc (Units.map σ.toRingEquiv.toMonoidHom y) ^ n
          = Units.map σ.toRingEquiv.toMonoidHom (y ^ n) := (map_pow _ _ _).symm
        _ = Units.map σ.toRingEquiv.toMonoidHom ((tateUnit T b) ^ m) := by rw [← hm]
        _ = (Units.map σ.toRingEquiv.toMonoidHom (tateUnit T b)) ^ m := map_zpow _ _ _
        _ = (tateUnit T b) ^ m := by
              rw [tateParameterUnit_algEquiv_map (sectionKPlace T b) (tateQ T b)
                (sectionQ T b).q_ne_zero σ]
        _ = y ^ n := hm
    rw [div_pow, h1]
    exact div_eq_one.mpr rfl
  -- 6. q_v ^ Z intersect mu_n = 1, so σ y = y
  have hσone : ∀ σ : GalK T b, Units.map σ.toRingEquiv.toMonoidHom y = y := by
    intro σ
    obtain ⟨j, hj⟩ := hσdiv σ
    have hjpow : ((tateUnit T b) ^ j) ^ n = 1 := by
      have h5 := hσpow σ
      rwa [hj] at h5
    have hj0 : j = 0 := tateUnit_zpow_eq_one_of_pow_eq_one T b hn hjpow
    have h1 : Units.map σ.toRingEquiv.toMonoidHom y / y = 1 := by
      rw [hj, hj0, zpow_zero]
    exact div_eq_one.mp h1
  -- 7. y is fixed by the absolute Galois group, hence lies in K_v
  have hrange : (y : LK T b) ∈ Set.range (algebraMap (Kv T b) (LK T b)) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (y : LK T b)).mpr ?_
    intro σ
    have h1 := congrArg Units.val (hσone σ)
    simpa using h1
  obtain ⟨a, ha⟩ := hrange
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact Units.ne_zero y ha.symm
  -- 8. package the representative and its exponent
  let x : (Kv T b)ˣ := Units.mk0 a ha0
  have hx : unitsMap T b x = y := by
    apply Units.ext
    rw [Units.coe_map]
    simpa [x] using ha
  have hval1 : (y : LK T b) ^ n = ((tateUnit T b ^ m : (LK T b)ˣ) : LK T b) := by
    have h8 := congrArg Units.val hm
    rw [Units.val_pow_eq_pow_val] at h8
    exact h8.symm
  have hval2 : ((tateUnit T b ^ m : (LK T b)ˣ) : LK T b) =
      (algebraMap (Kv T b) (LK T b)) ((tateQ T b) ^ m) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    rfl
  refine ⟨x, m, ?_, ?_⟩
  · rw [hx, hyP]
  · apply (algebraMap (Kv T b) (LK T b)).injective
    rw [map_pow]
    rw [show (algebraMap (Kv T b) (LK T b)) (x : Kv T b) = (y : LK T b) from by
      have h6 := congrArg Units.val hx
      simpa using h6]
    rw [hval1, hval2]

/-! ## 3. Parity: an even exponent only gives the -1 class -/

/-- The -1 of the completion, as a unit. -/
noncomputable def negOneUnit : (Kv T b)ˣ := Units.mk0 (-1) (by norm_num)

/-- The K-side Tate point represented by the unit -1. -/
noncomputable def negOneTatePoint : SideKPoint T b :=
  (pointEquiv T b (QuotientGroup.mk (unitsMap T b (negOneUnit T b)))).toAdd

/-- If the exponent of a 2-torsion representative is even, the point is either
zero or the point represented by -1. -/
theorem twoTorsion_of_even_exponent (P : SideKPoint T b) (x : (Kv T b)ˣ) (m : Int)
    (hm : Even m)
    (hclass : pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P)
    (hpow : (x : Kv T b) ^ 2 = (tateQ T b) ^ m) :
    P = 0 ∨ P = negOneTatePoint T b := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : Int, m = 2 * k := by
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, by rw [hk]; ring⟩
  have hq : (tateQ T b) ≠ 0 := (sectionQ T b).q_ne_zero
  have hqk : (tateQ T b) ^ k ≠ 0 := zpow_ne_zero k hq
  have hsq : ((x : Kv T b) / (tateQ T b) ^ k) ^ 2 = 1 := by
    have h2 : ((tateQ T b) ^ k) ^ 2 = (tateQ T b) ^ (2 * k) := by
      rw [sq, ← zpow_add₀ hq]
      congr 1
      ring
    rw [div_pow, hpow, hk, ← h2]
    exact div_self (pow_ne_zero 2 hqk)
  have hcases : (x : Kv T b) / (tateQ T b) ^ k = 1 ∨
      (x : Kv T b) / (tateQ T b) ^ k = -1 := by
    have h3 : ((x : Kv T b) / (tateQ T b) ^ k - 1) *
        ((x : Kv T b) / (tateQ T b) ^ k + 1) = 0 := by
      have h4 : ((x : Kv T b) / (tateQ T b) ^ k) ^ 2 - 1 = 0 := by rw [hsq]; ring
      calc ((x : Kv T b) / (tateQ T b) ^ k - 1) * ((x : Kv T b) / (tateQ T b) ^ k + 1)
          = ((x : Kv T b) / (tateQ T b) ^ k) ^ 2 - 1 := by ring
        _ = 0 := h4
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact Or.inl (sub_eq_zero.mp h4)
    · exact Or.inr (add_eq_zero_iff_eq_neg.mp h4)
  have htu : tateUnit T b = unitsMap T b (Units.mk0 (tateQ T b) (sectionQ T b).q_ne_zero) := rfl
  have hqk_unit : (Units.mk0 (tateQ T b) (sectionQ T b).q_ne_zero) ^ k =
      Units.mk0 ((tateQ T b) ^ k) hqk := by
    apply Units.ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0]
  have hmk_of : ∀ z : (LK T b)ˣ, z ∈ Subgroup.zpowers (tateUnit T b) →
      QuotientGroup.mk z = (1 : DeckK T b) := by
    intro z hz
    exact (QuotientGroup.eq_one_iff z).mpr hz
  rcases hcases with h4 | h4
  · -- x = q^k
    have hx1 : (x : Kv T b) = (tateQ T b) ^ k := by
      have h6 := h4
      rw [div_eq_iff hqk] at h6
      simpa using h6
    have hxu : x = Units.mk0 ((tateQ T b) ^ k) hqk := by
      apply Units.ext
      rw [Units.val_mk0]
      exact hx1
    have hu : unitsMap T b x = (tateUnit T b) ^ k := by
      rw [hxu, ← hqk_unit, map_zpow, ← htu]
    left
    have hmk1 : QuotientGroup.mk (unitsMap T b x) = (1 : DeckK T b) := by
      rw [hu]
      exact hmk_of _ (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    have hP1 : Multiplicative.ofAdd P = 1 := by
      rw [← hclass, hmk1, map_one]
    have h7 := congrArg Multiplicative.toAdd hP1
    simpa using h7
  · -- x = -q^k
    have hx2 : (x : Kv T b) = -((tateQ T b) ^ k) := by
      have h6 := h4
      rw [div_eq_iff hqk] at h6
      simpa using h6
    have hxu : x = negOneUnit T b * Units.mk0 ((tateQ T b) ^ k) hqk := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mk0]
      rw [show ((negOneUnit T b : Kv T b)) = -1 from rfl, hx2]
      ring
    have hu : unitsMap T b x = unitsMap T b (negOneUnit T b) * (tateUnit T b) ^ k := by
      rw [hxu, map_mul, ← hqk_unit, map_zpow, ← htu]
    right
    have hmk2 : QuotientGroup.mk (unitsMap T b x) =
        (QuotientGroup.mk (unitsMap T b (negOneUnit T b)) : DeckK T b) := by
      rw [hu, QuotientGroup.mk_mul,
        hmk_of _ (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)]
      exact mul_one (QuotientGroup.mk (unitsMap T b (negOneUnit T b)) : DeckK T b)
    have hP2 : Multiplicative.ofAdd P = Multiplicative.ofAdd (negOneTatePoint T b) := by
      rw [← hclass, hmk2]
      rfl
    have h7 := congrArg Multiplicative.toAdd hP2
    simpa using h7


/-! ## 4. Three rational 2-torsion points give the square source -/

/-- Among three distinct 2-torsion points with base-unit representatives, one
has odd exponent. -/
theorem three_twoTorsion_odd_exponent
    (P₁ P₂ P₃ : SideKPoint T b)
    (hne₁₂ : P₁ ≠ P₂) (hne₁₃ : P₁ ≠ P₃) (hne₂₃ : P₂ ≠ P₃)
    (h₁ : ∃ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P₁ ∧
      (x : Kv T b) ^ 2 = (tateQ T b) ^ m)
    (h₂ : ∃ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P₂ ∧
      (x : Kv T b) ^ 2 = (tateQ T b) ^ m)
    (h₃ : ∃ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P₃ ∧
      (x : Kv T b) ^ 2 = (tateQ T b) ^ m) :
    (∃ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P₁ ∧
      (x : Kv T b) ^ 2 = (tateQ T b) ^ m ∧ Odd m) ∨
    (∃ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P₂ ∧
      (x : Kv T b) ^ 2 = (tateQ T b) ^ m ∧ Odd m) ∨
    (∃ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P₃ ∧
      (x : Kv T b) ^ 2 = (tateQ T b) ^ m ∧ Odd m) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h₁', h₂', h₃'⟩ := hcon
  obtain ⟨x₁, m₁, hc₁, hp₁⟩ := h₁
  obtain ⟨x₂, m₂, hc₂, hp₂⟩ := h₂
  obtain ⟨x₃, m₃, hc₃, hp₃⟩ := h₃
  have he₁ : Even m₁ := Int.not_odd_iff_even.mp (h₁' x₁ m₁ hc₁ hp₁)
  have he₂ : Even m₂ := Int.not_odd_iff_even.mp (h₂' x₂ m₂ hc₂ hp₂)
  have he₃ : Even m₃ := Int.not_odd_iff_even.mp (h₃' x₃ m₃ hc₃ hp₃)
  have hP₁ := twoTorsion_of_even_exponent T b P₁ x₁ m₁ he₁ hc₁ hp₁
  have hP₂ := twoTorsion_of_even_exponent T b P₂ x₂ m₂ he₂ hc₂ hp₂
  have hP₃ := twoTorsion_of_even_exponent T b P₃ x₃ m₃ he₃ hc₃ hp₃
  rcases hP₁ with hP₁ | hP₁ <;> rcases hP₂ with hP₂ | hP₂ <;>
    rcases hP₃ with hP₃ | hP₃ <;> simp_all

/-- **The square source condition from three distinct nonzero Galois-fixed
2-torsion points** of the K-side Tate group. -/
theorem S2190QSquareSource_of_three_twoTorsion
    (P₁ P₂ P₃ : SideKPoint T b)
    (hne₁₂ : P₁ ≠ P₂) (hne₁₃ : P₁ ≠ P₃) (hne₂₃ : P₂ ≠ P₃)
    (hfix₁ : IsGaloisFixed T b P₁) (hfix₂ : IsGaloisFixed T b P₂)
    (hfix₃ : IsGaloisFixed T b P₃)
    (ht₁ : (2 : Nat) • P₁ = 0) (ht₂ : (2 : Nat) • P₂ = 0) (ht₃ : (2 : Nat) • P₃ = 0) :
    S2190QSquareSource T b := by
  have h₁ := tateDescent T b P₁ 2 (by norm_num) hfix₁ ht₁
  have h₂ := tateDescent T b P₂ 2 (by norm_num) hfix₂ ht₂
  have h₃ := tateDescent T b P₃ 2 (by norm_num) hfix₃ ht₃
  obtain ⟨x, m, hc, hp, hm⟩ | ⟨x, m, hc, hp, hm⟩ | ⟨x, m, hc, hp, hm⟩ :=
    three_twoTorsion_odd_exponent T b P₁ P₂ P₃ hne₁₂ hne₁₃ hne₂₃ h₁ h₂ h₃
  · exact sqrt_of_odd_zpow (tateQ T b) (sectionQ T b).q_ne_zero x m hp hm
  · exact sqrt_of_odd_zpow (tateQ T b) (sectionQ T b).q_ne_zero x m hp hm
  · exact sqrt_of_odd_zpow (tateQ T b) (sectionQ T b).q_ne_zero x m hp hm

/-- The exact geometric input for the square source condition: three distinct
nonzero Galois-fixed 2-torsion points of the K-side Tate point group.

Clause (c) of the source supplies the F-rational 2*3-torsion; the missing
transport is from those F-rational points to fixed points of the absolute
Galois group of K_v on the K-side curve. -/
def S2296ThreeRationalTwoTorsion : Prop :=
  ∃ P₁ P₂ P₃ : SideKPoint T b,
    P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₂ ≠ P₃ ∧ P₁ ≠ 0 ∧ P₂ ≠ 0 ∧ P₃ ≠ 0 ∧
    IsGaloisFixed T b P₁ ∧ IsGaloisFixed T b P₂ ∧ IsGaloisFixed T b P₃ ∧
    (2 : Nat) • P₁ = 0 ∧ (2 : Nat) • P₂ = 0 ∧ (2 : Nat) • P₃ = 0

/-- The three-point geometric input gives the square source condition. -/
theorem S2190QSquareSource_of_threeRationalTwoTorsion
    (h : S2296ThreeRationalTwoTorsion T b) : S2190QSquareSource T b := by
  obtain ⟨P₁, P₂, P₃, h12, h13, h23, -, -, -, hf1, hf2, hf3, ht1, ht2, ht3⟩ := h
  exact S2190QSquareSource_of_three_twoTorsion T b P₁ P₂ P₃ h12 h13 h23 hf1 hf2 hf3
    ht1 ht2 ht3

/-- **The clause-(b) bridge of S2190 reduced to an explicit geometric
statement.**  If the F-rational 2*3-torsion of clause (c) transports to three
distinct nonzero Galois-fixed 2-torsion points of the K-side Tate group, then
q_v is a square. -/
theorem S2190TwoTorsionToQSqrtBridge_of_threeRationalTwoTorsion
    (h : PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve →
      S2296ThreeRationalTwoTorsion T b) :
    S2190TwoTorsionToQSqrtBridge T b :=
  fun _ => S2190QSquareSource_of_threeRationalTwoTorsion T b
    (h T.clauseC.torsion23_rational)

/-! ## 5. The l-torsion side -/

/-- The units map of an integral power of q_v is the corresponding power of the
Tate unit. -/
theorem unitsMap_tateQ_zpow (k : Int) :
    unitsMap T b (Units.mk0 ((tateQ T b) ^ k)
        (zpow_ne_zero k (sectionQ T b).q_ne_zero)) = (tateUnit T b) ^ k := by
  have hqk_unit : (Units.mk0 (tateQ T b) (sectionQ T b).q_ne_zero) ^ k =
      Units.mk0 ((tateQ T b) ^ k) (zpow_ne_zero k (sectionQ T b).q_ne_zero) := by
    apply Units.ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0]
  rw [← hqk_unit, map_zpow]
  rfl

/-- An integral power of q_v is trivial in the Tate quotient. -/
theorem mk_unitsMap_tateQ_zpow (k : Int) :
    QuotientGroup.mk (unitsMap T b (Units.mk0 ((tateQ T b) ^ k)
      (zpow_ne_zero k (sectionQ T b).q_ne_zero))) = (1 : DeckK T b) := by
  rw [unitsMap_tateQ_zpow T b k]
  exact (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)

/-- An integral power of the Tate unit is trivial in the Tate quotient. -/
theorem mk_tateUnit_zpow (k : Int) :
    QuotientGroup.mk ((tateUnit T b) ^ k) = (1 : DeckK T b) :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)

/-- If l divides the exponent of a representative of an l-torsion class, the
class is the class of an l-th root of unity in K_v. -/
theorem lTorsion_class_eq_rootOfUnity
    (P : SideKPoint T b) (x : (Kv T b)ˣ) (m : Int)
    (hclass : pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P)
    (hpow : (x : Kv T b) ^ l.value = (tateQ T b) ^ m)
    (hdvd : (l.value : Int) ∣ m) :
    ∃ ζ : (Kv T b)ˣ, (ζ : Kv T b) ^ l.value = 1 ∧
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) =
        pointEquiv T b (QuotientGroup.mk (unitsMap T b ζ)) := by
  classical
  obtain ⟨k, hk⟩ := hdvd
  have hq : (tateQ T b) ≠ 0 := (sectionQ T b).q_ne_zero
  have hqk : (tateQ T b) ^ k ≠ 0 := zpow_ne_zero k hq
  have hxne : (x : Kv T b) ≠ 0 := Units.ne_zero x
  set η : (Kv T b)ˣ := Units.mk0 ((x : Kv T b) / (tateQ T b) ^ k)
    (div_ne_zero hxne hqk) with hη
  refine ⟨η, ?_, ?_⟩
  · rw [hη, Units.val_mk0, div_pow, hpow, hk]
    rw [show ((tateQ T b) ^ k) ^ l.value = (tateQ T b) ^ (k * (l.value : Int)) from by
      rw [← zpow_natCast, zpow_mul]]
    rw [mul_comm (l.value : Int) k]
    exact div_self (zpow_ne_zero (k * (l.value : Int)) hq)
  · have hxunit : x = η * Units.mk0 ((tateQ T b) ^ k) hqk := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_mk0, hη]
      exact (div_mul_cancel₀ (x : Kv T b) hqk).symm
    have hmap : unitsMap T b x = unitsMap T b η * (tateUnit T b) ^ k := by
      rw [hxunit, map_mul, unitsMap_tateQ_zpow T b k]
    have hmk : QuotientGroup.mk (unitsMap T b x) = (QuotientGroup.mk (unitsMap T b η) : DeckK T b) := by
      rw [hmap, QuotientGroup.mk_mul, mk_tateUnit_zpow T b k]
      exact mul_one (QuotientGroup.mk (unitsMap T b η) : DeckK T b)
    rw [hmk]

/-- An integer not divisible by the prime l is coprime to it. -/
theorem coprime_of_not_dvd {m : Int} (hm : ¬ (l.value : Int) ∣ m) :
    Nat.Coprime l.value m.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  have hdvd : Nat.gcd l.value m.natAbs ∣ l.value := Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime l.prime).mp hdvd with h1 | h1
  · exact h h1
  · exfalso
    apply hm
    have h2 : l.value ∣ m.natAbs := by rw [← h1]; exact Nat.gcd_dvd_right _ _
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h2)

/-- **The l-th power source condition from a non-l-divisible exponent.** -/
theorem S2190QLthPowerSource_of_not_dvd (x : (Kv T b)ˣ) (m : Int)
    (hpow : (x : Kv T b) ^ l.value = (tateQ T b) ^ m) (hm : ¬ (l.value : Int) ∣ m) :
    S2190QLthPowerSource T b :=
  lthRoot_of_coprime_zpow l.value (tateQ T b) (sectionQ T b).q_ne_zero x m hpow
    (coprime_of_not_dvd hm)

/-- The exact remaining input for the l-th power source condition: a
Galois-fixed l-torsion class with a base-unit representative whose exponent is
prime to l. -/
def S2296LCoprimeRepresentative : Prop :=
  ∃ (P : SideKPoint T b) (x : (Kv T b)ˣ) (m : Int),
    IsGaloisFixed T b P ∧ l.value • P = 0 ∧
    pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P ∧
    (x : Kv T b) ^ l.value = (tateQ T b) ^ m ∧ Nat.Coprime l.value m.natAbs

/-- The l-torsion coprime representative gives the l-th power source
condition. -/
theorem S2190QLthPowerSource_of_LCoprimeRepresentative
    (h : S2296LCoprimeRepresentative T b) : S2190QLthPowerSource T b := by
  obtain ⟨P, x, m, -, -, -, hpow, hcop⟩ := h
  exact lthRoot_of_coprime_zpow l.value (tateQ T b) (sectionQ T b).q_ne_zero x m hpow hcop

/-- The l-th power source condition from an l-torsion class whose exponent is
not divisible by l. -/
theorem S2190QLthPowerSource_of_lTorsion_class (P : SideKPoint T b)
    (hfix : IsGaloisFixed T b P) (htors : l.value • P = 0) :
    (∀ (x : (Kv T b)ˣ) (m : Int),
      pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P →
      (x : Kv T b) ^ l.value = (tateQ T b) ^ m → ¬ (l.value : Int) ∣ m) →
    S2190QLthPowerSource T b := by
  intro h
  obtain ⟨x, m, hc, hp⟩ := tateDescent T b P l.value l.prime.pos hfix htors
  exact S2190QLthPowerSource_of_not_dvd T b x m hp (h x m hc hp)

/-! ## 6. The S2223 Tate parameters and the two source conditions -/

/-- The two-torsion Tate parameter of S2223 from an odd exponent. -/
noncomputable def twoTorsionTateParameter_of_odd_exponent
    (P : SideKPoint T b) (h2 : (2 : Nat) • P = 0)
    (x : (Kv T b)ˣ) (m : Int)
    (hclass : pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P)
    (hpow : (x : Kv T b) ^ 2 = (tateQ T b) ^ m) (hm : Odd m) :
    S2223TwoTorsionTateParameter T b where
  P := P
  point_two_torsion := h2
  x := x
  m := m
  class_eq := hclass
  pow_eq := hpow
  m_odd := hm

/-- The l-torsion Tate parameter of S2223 from a coprime representative. -/
noncomputable def lTorsionTateParameter_of_coprime
    (P : SideKPoint T b) (h2 : l.value • P = 0)
    (x : (Kv T b)ˣ) (m : Int)
    (hclass : pointEquiv T b (QuotientGroup.mk (unitsMap T b x)) = Multiplicative.ofAdd P)
    (hpow : (x : Kv T b) ^ l.value = (tateQ T b) ^ m)
    (hm : Nat.Coprime l.value m.natAbs) :
    S2223LTorsionTateParameter T b where
  P := P
  point_l_torsion := h2
  x := x
  m := m
  class_eq := hclass
  pow_eq := hpow
  m_coprime := hm

/-- The three-point geometric input yields the S2223 two-torsion Tate
parameter. -/
theorem nonempty_twoTorsionTateParameter_of_three
    (h : S2296ThreeRationalTwoTorsion T b) :
    Nonempty (S2223TwoTorsionTateParameter T b) := by
  obtain ⟨P₁, P₂, P₃, h12, h13, h23, -, -, -, hf1, hf2, hf3, ht1, ht2, ht3⟩ := h
  have h₁ := tateDescent T b P₁ 2 (by norm_num) hf1 ht1
  have h₂ := tateDescent T b P₂ 2 (by norm_num) hf2 ht2
  have h₃ := tateDescent T b P₃ 2 (by norm_num) hf3 ht3
  obtain ⟨x, m, hc, hp, hm⟩ | ⟨x, m, hc, hp, hm⟩ | ⟨x, m, hc, hp, hm⟩ :=
    three_twoTorsion_odd_exponent T b P₁ P₂ P₃ h12 h13 h23 h₁ h₂ h₃
  · exact ⟨twoTorsionTateParameter_of_odd_exponent T b P₁ ht1 x m hc hp hm⟩
  · exact ⟨twoTorsionTateParameter_of_odd_exponent T b P₂ ht2 x m hc hp hm⟩
  · exact ⟨twoTorsionTateParameter_of_odd_exponent T b P₃ ht3 x m hc hp hm⟩

/-- The l-torsion coprime representative yields the S2223 l-torsion Tate
parameter. -/
theorem nonempty_lTorsionTateParameter_of_LCoprimeRepresentative
    (h : S2296LCoprimeRepresentative T b) :
    Nonempty (S2223LTorsionTateParameter T b) := by
  obtain ⟨P, x, m, -, htors, hc, hp, hcop⟩ := h
  exact ⟨lTorsionTateParameter_of_coprime T b P htors x m hc hp hcop⟩

/-- **The S2223 base-unit descent from the two geometric inputs.** -/
theorem S2223TateBaseUnitDescent_of_geometric
    (h2 : S2296ThreeRationalTwoTorsion T b) (hl : S2296LCoprimeRepresentative T b) :
    S2223TateBaseUnitDescent T b :=
  ⟨nonempty_twoTorsionTateParameter_of_three T b h2,
    nonempty_lTorsionTateParameter_of_LCoprimeRepresentative T b hl⟩

/-- Consequently both S2190 source conditions hold from the two geometric
inputs. -/
theorem S2190HalfRootSource_of_geometric
    (h2 : S2296ThreeRationalTwoTorsion T b) (hl : S2296LCoprimeRepresentative T b) :
    S2190HalfRootSource T b :=
  halfRootSource_of_tateBaseUnitDescent T b
    (S2223TateBaseUnitDescent_of_geometric T b h2 hl)

/-! ## 7. Axiom audit -/

#print axioms tateQ_nat_pow_ne_one
#print axioms tateQ_zpow_eq_one
#print axioms tateUnit_zpow_eq_one
#print axioms tateUnit_zpow_eq_one_of_pow_eq_one
#print axioms tateDescent
#print axioms twoTorsion_of_even_exponent
#print axioms three_twoTorsion_odd_exponent
#print axioms S2190QSquareSource_of_three_twoTorsion
#print axioms S2190QSquareSource_of_threeRationalTwoTorsion
#print axioms S2190TwoTorsionToQSqrtBridge_of_threeRationalTwoTorsion
#print axioms unitsMap_tateQ_zpow
#print axioms mk_unitsMap_tateQ_zpow
#print axioms lTorsion_class_eq_rootOfUnity
#print axioms coprime_of_not_dvd
#print axioms S2190QLthPowerSource_of_not_dvd
#print axioms S2190QLthPowerSource_of_LCoprimeRepresentative
#print axioms S2190QLthPowerSource_of_lTorsion_class
#print axioms nonempty_twoTorsionTateParameter_of_three
#print axioms nonempty_lTorsionTateParameter_of_LCoprimeRepresentative
#print axioms S2223TateBaseUnitDescent_of_geometric
#print axioms S2190HalfRootSource_of_geometric

end LeanFormal.IUT.XiFPaper.S2296TateBaseUnitActual
