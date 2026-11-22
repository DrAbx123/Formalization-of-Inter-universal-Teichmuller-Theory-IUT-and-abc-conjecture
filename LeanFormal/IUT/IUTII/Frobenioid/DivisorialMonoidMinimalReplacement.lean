/-
  Minimal replacement for the missing sharp divisorial monoid of the source
  carrier: the nonnegative cone of a value group.

  Frobenioids I, Definition 1.1(i), defines a pre-divisorial monoid to be an
  integral, saturated monoid of characteristic type, and the divisorial
  monoids are the sharp pre-divisorial monoids; the paper's standard example
  is the monoid of effective divisors of a log scheme, whose only additive
  unit is the trivial divisor ([FrdI] Section 0; corpus lines 443ff and
  810ff).  The current prime-strip carriers of this repository are
  group-valued, and `PrimeStripFrobenioidCards.lean` proves that they cannot
  carry a sharp divisorial monoid (`not_sharp_of_addGroup`,
  `frobenioidLinkUnitStrip_not_sharp`); `PrimeStripFrobenioidCategorySkeleton.lean`
  (lines 58ff) records the divisor side of the Frobenius data as blocked by
  this missing object, with the card at
  `PrimeStripFrobenioidSkeletonCards.lean:137`.

  This file supplies the minimal concrete replacement over the value group
  `Q` of a completed p-adic algebraic closure (the value group of `Qbar_p`):

  * `nonnegativeRationalDivisorialAddMonoid` -- the nonnegative cone `Q>=0`
    as a sharp divisorial monoid in the sense of [FrdI] Definition 1.1(i)
    (divisorial = sharp case): integral, sharp, saturated;
  * `nnratGrothendieckAddEquivRat` -- its Grothendieck group is the value
    group `Q`, i.e. the divisor monoid is exactly the nonnegative cone
    inside its value group (`nnratGrothendieckToRat_nonneg_iff_mem_range`);
  * `divisorFrobeniusNSMul` -- the value-side Frobenius action on the divisor
    monoid (`a |-> n . a`), the additive counterpart of the multiplicative
    fragment `valueFrobeniusPower` (`x |-> x^n`) of
    `PrimeStripFrobenioidCategorySkeleton.lean`, with the group-completion
    compatibility `of (n . a) = n . of a` ([FrdI] Proposition 2.1(i)-(ii);
    corpus lines 1958ff);
  * `singleFibreDivisorialMonoidOn` -- a one-fibre inhabitant of
    `Iut.DivisorialMonoidOn` ([FrdI] Definition 1.1(i)-(ii) functoriality
    layer) over the constant fibre `Q>=0`.

  The source-specific carrier (a sharp divisorial monoid on the source base
  with its characteristic type, Qbar_p-level analytic structure and the
  log-shell compatibility) is not constructed here; see Entry 19 of
  `logs/coordination/finrank-ef-20261016.md` for the precise remaining gap
  statement.
-/

import Iut.Foundations.Frobenioid
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Tactic

namespace LeanFormal.IUT

noncomputable section

namespace DivisorialMonoidMinimalReplacement

open Algebra

/-! ## 0. The sharpness obstruction on a group

The carrier of a sharp divisorial monoid can never be an additive group: in
a group every element is an additive unit, so sharpness forces the carrier to
be trivial.  This is the formal reason why the source carrier must be the
nonnegative cone of the value group rather than the value group itself; it
is the additive-group form of the prime-strip negative results recorded in
`PrimeStripFrobenioidCards.lean`. -/

/-- In an additive commutative group, sharpness (`IsAddUnit a -> a = 0` for
every `a`) forces the group to be a subsingleton. -/
theorem subsingleton_of_sharp_of_addCommGroup {α : Type*} [AddCommGroup α]
    (hsharp : ∀ a : α, IsAddUnit a → a = 0) : Subsingleton α := by
  refine ⟨fun a b => ?_⟩
  have h0 : ∀ a : α, a = 0 := fun a =>
    hsharp a ⟨AddUnits.mk a (-a) (add_neg_cancel a) (neg_add_cancel a), rfl⟩
  rw [h0 a, h0 b]

/-! ## 1. The sharpness law on `Q>=0` -/

/-- On the nonnegative rationals, a vanishing sum has vanishing left
summand. -/
theorem nnrat_left_eq_zero_of_add_eq_zero {a b : ℚ≥0} (h : a + b = 0) :
    a = 0 := by
  have hco : (a : ℚ) + (b : ℚ) = 0 := by
    rw [← NNRat.coe_add, h, NNRat.coe_zero]
  have ha : (0 : ℚ) ≤ (a : ℚ) := NNRat.coe_nonneg a
  have hb : (0 : ℚ) ≤ (b : ℚ) := NNRat.coe_nonneg b
  apply NNRat.ext
  rw [NNRat.coe_zero]
  linarith

/-- The sharpness law of `Q>=0`: additive units vanish.  This is the
`M^pm = 0` condition of the divisorial case in [FrdI] Section 0. -/
theorem nnrat_eq_zero_of_isAddUnit {a : ℚ≥0} (h : IsAddUnit a) : a = 0 := by
  obtain ⟨b, hb⟩ := h.exists_neg
  exact nnrat_left_eq_zero_of_add_eq_zero hb

/-! ## 2. The group completion of `Q>=0` is the value group `Q` -/

/-- The canonical additive homomorphism from the Grothendieck group of
`Q>=0` to the value group `Q`, induced by the coefficient map. -/
noncomputable def nnratGrothendieckToRat :
    Algebra.GrothendieckAddGroup ℚ≥0 →+ ℚ :=
  Algebra.GrothendieckAddGroup.lift ((NNRat.coeHom : ℚ≥0 →+* ℚ).toAddMonoidHom)

/-- On the image of the divisor monoid the comparison map is the
coefficient. -/
@[simp]
theorem nnratGrothendieckToRat_of (q : ℚ≥0) :
    nnratGrothendieckToRat (Algebra.GrothendieckAddGroup.of q) = (q : ℚ) := by
  have equality :=
    (Algebra.GrothendieckAddGroup.lift (M := ℚ≥0) (G := ℚ)).symm_apply_apply
      ((NNRat.coeHom : ℚ≥0 →+* ℚ).toAddMonoidHom)
  exact DFunLike.congr_fun equality q

/-- Representative computation in the group completion: `mk a s + of s` is
`of a`; equivalently `mk a s` is the difference `of a - of s`.  Elementwise
form of `mk_eq_monoidOf_mk'` at the top submonoid. -/
theorem nnratGrothendieck_mk_add_of (a : ℚ≥0) (s : (⊤ : AddSubmonoid ℚ≥0)) :
    AddLocalization.mk a s + Algebra.GrothendieckAddGroup.of s.1 =
      Algebra.GrothendieckAddGroup.of a := by
  change AddLocalization.mk a s +
      AddLocalization.mk s.1 (0 : (⊤ : AddSubmonoid ℚ≥0)) =
    AddLocalization.mk a (0 : (⊤ : AddSubmonoid ℚ≥0))
  rw [AddLocalization.mk_add]
  apply AddLocalization.mk_eq_mk_iff'.mpr
  rw [AddSubmonoid.coe_zero, AddSubmonoid.coe_add, AddSubmonoid.coe_zero,
    zero_add, add_zero]
  exact add_comm _ _

/-- The value of the comparison map on the representative `mk a s` is the
difference of coefficients. -/
theorem nnratGrothendieckToRat_mk (a : ℚ≥0) (s : (⊤ : AddSubmonoid ℚ≥0)) :
    nnratGrothendieckToRat (AddLocalization.mk a s) = (a : ℚ) - (s.1 : ℚ) := by
  have h := congrArg nnratGrothendieckToRat (nnratGrothendieck_mk_add_of a s)
  rw [map_add, nnratGrothendieckToRat_of, nnratGrothendieckToRat_of] at h
  linarith

/-- The image of the divisor monoid inside its group completion is exactly
the nonnegative cone of the value group: `x` lies in the image of `of` if
and only if its value is nonnegative.  This is the sense in which the
minimal sharp divisorial monoid sits inside its value group `Q`. -/
theorem nnratGrothendieckToRat_nonneg_iff_mem_range
    (x : Algebra.GrothendieckAddGroup ℚ≥0) :
    x ∈ Set.range (Algebra.GrothendieckAddGroup.of (M := ℚ≥0)) ↔
      0 ≤ nnratGrothendieckToRat x := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [nnratGrothendieckToRat_of]
    exact NNRat.coe_nonneg q
  · refine AddLocalization.ind (p := fun x =>
      (0 ≤ nnratGrothendieckToRat x) →
      x ∈ Set.range (Algebra.GrothendieckAddGroup.of (M := ℚ≥0))) ?_ x
    intro y hy
    rw [nnratGrothendieckToRat_mk] at hy
    let e : ℚ≥0 := Rat.toNNRat ((y.1 : ℚ) - (y.2.1 : ℚ))
    have he_coe : (e : ℚ) = (y.1 : ℚ) - (y.2.1 : ℚ) :=
      Rat.coe_toNNRat _ hy
    have hse : y.2.1 + e = y.1 := by
      apply NNRat.ext
      rw [NNRat.coe_add, he_coe]
      ring
    refine ⟨e, ?_⟩
    have hcomp : AddLocalization.mk y.1 y.2 =
        Algebra.GrothendieckAddGroup.of y.1 -
          Algebra.GrothendieckAddGroup.of y.2.1 :=
      eq_sub_of_add_eq (nnratGrothendieck_mk_add_of y.1 y.2)
    rw [hcomp]
    have hsplit : Algebra.GrothendieckAddGroup.of y.1 =
        Algebra.GrothendieckAddGroup.of y.2.1 +
          Algebra.GrothendieckAddGroup.of e := by
      rw [← hse, map_add]
    rw [hsplit]
    exact (add_sub_cancel_left _ _).symm

/-- `0` is the only element of the group completion whose value in both
directions is nonnegative. -/
theorem nnratGrothendieckToRat_eq_zero_iff
    (x : Algebra.GrothendieckAddGroup ℚ≥0) :
    nnratGrothendieckToRat x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx : 0 ≤ nnratGrothendieckToRat x := le_of_eq h.symm
    obtain ⟨a, ha⟩ := (nnratGrothendieckToRat_nonneg_iff_mem_range x).mpr hx
    have hx' : 0 ≤ nnratGrothendieckToRat (-x) := by
      rw [map_neg, h]
      simp
    obtain ⟨b, hb⟩ := (nnratGrothendieckToRat_nonneg_iff_mem_range (-x)).mpr hx'
    have hab : a + b = 0 := by
      have hsum : Algebra.GrothendieckAddGroup.of (a + b) = 0 := by
        rw [map_add, ha, hb]
        exact add_neg_cancel x
      have hsum' : Algebra.GrothendieckAddGroup.of (a + b) =
          Algebra.GrothendieckAddGroup.of (0 : ℚ≥0) := by
        simpa using hsum
      exact Algebra.GrothendieckAddGroup.of_injective hsum'
    have ha0 : a = 0 := nnrat_left_eq_zero_of_add_eq_zero hab
    rw [← ha, ha0]
    exact map_zero _
  · rintro rfl
    exact map_zero _

/-- The canonical comparison map is injective: the group completion of
`Q>=0` embeds into the value group. -/
theorem nnratGrothendieckToRat_injective :
    Function.Injective nnratGrothendieckToRat := by
  intro x y hxy
  have h : nnratGrothendieckToRat (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h0 := (nnratGrothendieckToRat_eq_zero_iff (x - y)).mp h
  exact sub_eq_zero.mp h0

/-- The canonical comparison map is surjective: every rational is a
difference `q - r` of nonnegative rationals. -/
theorem nnratGrothendieckToRat_surjective :
    Function.Surjective nnratGrothendieckToRat := by
  intro y
  refine ⟨Algebra.GrothendieckAddGroup.of (Rat.toNNRat (max y 0)) -
    Algebra.GrothendieckAddGroup.of (Rat.toNNRat (max (-y) 0)), ?_⟩
  rw [map_sub, nnratGrothendieckToRat_of, nnratGrothendieckToRat_of]
  rw [Rat.coe_toNNRat _ (le_max_right _ _),
    Rat.coe_toNNRat _ (le_max_right _ _)]
  rcases le_total 0 y with hle | hle
  · rw [max_eq_left hle, max_eq_right (neg_nonpos.mpr hle)]
    ring
  · rw [max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)]
    ring

/-- The group completion of the minimal sharp divisorial monoid is the
value group `Q`: the Grothendieck group of the nonnegative cone `Q>=0` is
`Q`, matching the value group of the completed p-adic algebraic closure
`Qbar_p`. -/
noncomputable def nnratGrothendieckAddEquivRat :
    Algebra.GrothendieckAddGroup ℚ≥0 ≃+ ℚ :=
  AddEquiv.ofBijective nnratGrothendieckToRat
    ⟨nnratGrothendieckToRat_injective, nnratGrothendieckToRat_surjective⟩

/-! ## 3. The minimal sharp divisorial monoid -/

/-- The minimal sharp divisorial monoid of the source-carrier card: the
nonnegative cone `Q>=0` of the value group `Q`, in the sense of [FrdI]
Definition 1.1(i) (divisorial = sharp case).  Integrality is additive
cancellation on coefficients; sharpness is `nnrat_eq_zero_of_isAddUnit`;
saturation is proved through the range description of the divisor monoid
inside the value group (`nnratGrothendieckToRat_nonneg_iff_mem_range`). -/
noncomputable def nonnegativeRationalDivisorialAddMonoid :
    Iut.DivisorialAddMonoid where
  carrier := ℚ≥0
  integral := fun a b c h => NNRat.coe_injective (by
    have h' : (a : ℚ) + (b : ℚ) = (a : ℚ) + (c : ℚ) := by
      simpa only [NNRat.coe_add] using congrArg (fun x : ℚ≥0 => (x : ℚ)) h
    linarith)
  sharp := fun _ h => nnrat_eq_zero_of_isAddUnit h
  saturated := by
    intro x n hx
    rw [nnratGrothendieckToRat_nonneg_iff_mem_range] at hx ⊢
    rw [map_nsmul] at hx
    rw [nsmul_eq_mul] at hx
    have hn : (0 : ℚ) < (n.1 : ℚ) := by exact_mod_cast n.2
    exact (mul_nonneg_iff_of_pos_left hn).mp hx

/-! ## 4. The Frobenius action on the divisor monoid

The value-side fragment of [FrdI] Definition 1.1(iii)/Proposition 2.1(i)-(ii)
on the divisor monoid: the Frobenius degree `n` acts additively by
`a |-> n . a`, mirroring `valueFrobeniusPower` (`x |-> x^n`) on the
multiplicative side, and this action extends to multiplication by the degree
on the value group. -/

/-- The Frobenius degree `n` acting on the divisor monoid `Q>=0` by
`a |-> n . a`. -/
noncomputable def divisorFrobeniusNSMul (n : ℕ+) : ℚ≥0 →+ ℚ≥0 where
  toFun a := n.1 • a
  map_zero' := nsmul_zero _
  map_add' a b := by rw [nsmul_add]

@[simp]
theorem divisorFrobeniusNSMul_apply (n : ℕ+) (a : ℚ≥0) :
    divisorFrobeniusNSMul n a = n.1 • a := rfl

/-- Degree `1` is the identity action. -/
theorem divisorFrobeniusNSMul_one :
    divisorFrobeniusNSMul 1 = AddMonoidHom.id ℚ≥0 := by
  refine AddMonoidHom.ext (fun a => ?_)
  exact one_nsmul a

/-- Composite Frobenius degrees compose: degree `m * n` acts as `m`
followed by `n`.  This is the additive counterpart of the degree law
`d1 * d2` of [FrdI] Proposition 2.1(i) (compare `valueFrobeniusPower_mul`). -/
theorem divisorFrobeniusNSMul_mul (m n : ℕ+) :
    divisorFrobeniusNSMul (m * n) =
      (divisorFrobeniusNSMul n).comp (divisorFrobeniusNSMul m) := by
  refine AddMonoidHom.ext (fun a => ?_)
  simp only [AddMonoidHom.comp_apply, divisorFrobeniusNSMul_apply, smul_smul]
  congr 1
  exact (PNat.mul_coe m n).trans (Nat.mul_comm _ _)

/-- The Frobenius action on the divisor monoid extends to multiplication
by the degree on the value group: `of (n . a) = n . of a`.  This is the
group-completion compatibility of the value-side fragment of [FrdI]
Proposition 2.1(ii). -/
theorem divisorFrobeniusNSMul_of (n : ℕ+) (a : ℚ≥0) :
    Algebra.GrothendieckAddGroup.of (divisorFrobeniusNSMul n a) =
      n.1 • Algebra.GrothendieckAddGroup.of a :=
  map_nsmul (Algebra.GrothendieckAddGroup.of (M := ℚ≥0)) n.1 a

/-! ## 5. A one-fibre `DivisorialMonoidOn` inhabitant -/

/-- The one-object base `SingleObj Nat` with the nonnegative-rational
divisorial monoid on its single fibre, constant pullbacks (the identity)
and every morphism declared FSM.  This exhibits the functorial layer of
[FrdI] Definition 1.1(i)-(ii) (`Iut.DivisorialMonoidOn`) as inhabited by
the minimal sharp divisorial monoid; the source-specific base category,
characteristic type and pullback fields for the Qbar_p-level categories
remain open. -/
noncomputable def singleFibreDivisorialMonoidOn :
    Iut.DivisorialMonoidOn (CategoryTheory.SingleObj ℕ)
      (fun {X Y : CategoryTheory.SingleObj ℕ} (_ : X ⟶ Y) => True) where
  obj := fun _ => nonnegativeRationalDivisorialAddMonoid
  pullback := fun _ => AddMonoidHom.id ℚ≥0
  pullback_id := fun _ => rfl
  pullback_comp := fun _ _ => AddMonoidHom.ext fun _ => rfl
  characteristicallyInjective := fun _ => Function.injective_id
  fsmPullbackIsIso := fun _ _ => Function.bijective_id

end DivisorialMonoidMinimalReplacement

end

end LeanFormal.IUT
