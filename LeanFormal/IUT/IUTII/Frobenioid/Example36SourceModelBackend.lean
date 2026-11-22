import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData
import Iut.Foundations.SourceModelFrobenioid
import Iut.Foundations.SourceModelFrobenioidPresentation
import Mathlib.Tactic

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# The actual SourceModelFrobenioid input/carrier backend of III Example 3.6

This module supplies the Layer-4a backend of the handoff: the concrete
Iut.SourceModelFrobenioid.Input attached to a number field F, built from the
actual place data of Example36NumberFieldPlaceData, together with the
dictionary between the model objects and the global ideal families of
Example36GlobalIdealFamily.

Boundary: this file constructs the backend input/carrier and the
object/divisor dictionary only.  It does not construct the source Hodge
theater, prime-strips, the global torsor category or the equivalence of
Example 3.6, and it does not identify any of these objects with an output of
the source.  The single-object bottom category is the model carrier of the
local dictionary; it is not the source base category.
-/

noncomputable section

universe u

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace SourceModelBackend

open CategoryTheory IsDedekindDomain NumberField

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The single-object bottom base category -/

/-- The bottom base category of the model carrier: one object, in the universe of
the coefficient field.  All its endomorphisms are the identity. -/
abbrev BottomBase : Type u := ULift.{u, 0} Unit

/-- The unique object of the bottom base category. -/
def bottomPoint : BottomBase := ULift.up ()

instance bottomBaseCategory : CategoryTheory.Category.{u, u} BottomBase where
  Hom _ _ := ULift.{u, 0} Unit
  id _ := ULift.up ()
  comp _ _ := ULift.up ()
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- The FSM predicate on the bottom base category: every arrow (there is only the
identity) is an FSM morphism. -/
def BottomFSM : ∀ {X Y : BottomBase}, (X ⟶ Y) → Prop := fun _ => True

/-- All endomorphisms of the bottom base category are identities. -/
theorem bottomBase_hom_eq_id {X : BottomBase} (f : X ⟶ X) : f = 𝟙 X := by
  cases f
  rfl

/-- The one-object/one-arrow bottom base category is connected. -/
instance bottomBase_isConnected :
    CategoryTheory.IsConnected BottomBase := by
  haveI : Nonempty BottomBase := ⟨bottomPoint⟩
  haveI : Subsingleton BottomBase := inferInstance
  exact CategoryTheory.isConnected_of_nonempty_and_subsingleton

/-- Every arrow of the one-arrow bottom base category is an epimorphism. -/
theorem bottomBase_arrow_epi
    {X Y : BottomBase} (f : X ⟶ Y) : Epi f := by
  obtain rfl : X = Y := Subsingleton.elim X Y
  rw [bottomBase_hom_eq_id f]
  infer_instance

/-! ## 2. The effective divisor cone -/

/-- The effective divisor cone of the model Frobenioid: finitely supported
nonnegative finite-place valuation exponents, together with nonnegative
archimedean coordinates -log(radius). -/
abbrev EffectiveDivisor (F : Type u) [Field F] [NumberField F] : Type u :=
  (HeightOneSpectrum (𝓞 F) →₀ ℕ) × (NumberField.InfinitePlace F → NNReal)

/-- Additive cancellation in the effective divisor cone. -/
theorem effectiveDivisor_add_left_cancel (a b c : EffectiveDivisor F)
    (h : a + b = a + c) : b = c := by
  have hfin : a.1 + b.1 = a.1 + c.1 := congrArg Prod.fst h
  have hinf : a.2 + b.2 = a.2 + c.2 := congrArg Prod.snd h
  apply Prod.ext
  · ext v
    have hv := congrArg (fun g : HeightOneSpectrum (𝓞 F) →₀ ℕ => g v) hfin
    simp only [Finsupp.add_apply] at hv
    exact Nat.add_left_cancel hv
  · funext w
    have hw := congrArg (fun x : NNReal => (x : ℝ)) (congrFun hinf w)
    simp only [Pi.add_apply, NNReal.coe_add] at hw
    exact NNReal.coe_injective (by linarith)

/-- Right cancellation in the effective divisor cone. -/
theorem effectiveDivisor_add_right_cancel (a b c : EffectiveDivisor F)
    (h : a + b = c + b) : a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact effectiveDivisor_add_left_cancel b a c h

/-- Sharpness of the cone: its only additive unit is zero. -/
theorem effectiveDivisor_sharp (a : EffectiveDivisor F) (h : IsAddUnit a) : a = 0 := by
  obtain ⟨b, hb⟩ := h.exists_neg
  have hfin : a.1 + b.1 = 0 := congrArg Prod.fst hb
  have hinf : a.2 + b.2 = 0 := congrArg Prod.snd hb
  apply Prod.ext
  · ext v
    change a.1 v = 0
    have hv := congrArg (fun g : HeightOneSpectrum (𝓞 F) →₀ ℕ => g v) hfin
    simp only [Finsupp.add_apply, Finsupp.zero_apply] at hv
    omega
  · funext w
    change a.2 w = 0
    have hw := congrArg (fun x : NNReal => (x : ℝ)) (congrFun hinf w)
    simp only [Pi.add_apply, Pi.zero_apply, NNReal.coe_add, NNReal.coe_zero] at hw
    have hb' : (0 : ℝ) ≤ (b.2 w : ℝ) := NNReal.coe_nonneg _
    apply NNReal.coe_injective
    rw [NNReal.coe_zero]
    linarith

/-- The explicit divisor group: arbitrary-sign finitely supported finite-place
integer exponents and arbitrary real archimedean coordinates. -/
abbrev ExplicitDivisor (F : Type u) [Field F] [NumberField F] : Type u :=
  (HeightOneSpectrum (𝓞 F) →₀ ℤ) × (NumberField.InfinitePlace F → ℝ)

/-- The canonical inclusion of the effective cone into the explicit divisor
group. -/
def effectiveToExplicit : EffectiveDivisor F →+ ExplicitDivisor F where
  toFun d :=
    (d.1.mapRange (fun n : ℕ => (n : ℤ)) (by simp),
      fun w => (d.2 w : ℝ))
  map_zero' := by
    apply Prod.ext
    · exact Finsupp.mapRange_zero (f := fun n : ℕ => (n : ℤ)) (hf := by simp)
    · funext w
      simp
  map_add' := by
    intro a b
    apply Prod.ext
    · change Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) (a.1 + b.1) =
        Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) a.1 +
          Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) b.1
      rw [Finsupp.mapRange_add (fun x y => Nat.cast_add x y)]
    · funext w
      simp only [Prod.snd_add, Pi.add_apply, NNReal.coe_add]

/-- The comparison map from the Grothendieck group of the effective cone to the
explicit divisor group. -/
def coneComparison :
    Algebra.GrothendieckAddGroup (EffectiveDivisor F) →+ ExplicitDivisor F :=
  Algebra.GrothendieckAddGroup.lift effectiveToExplicit

/-- The comparison map extends the inclusion of the cone. -/
@[simp]
theorem coneComparison_of (x : EffectiveDivisor F) :
    coneComparison (Algebra.GrothendieckAddGroup.of x) = effectiveToExplicit x := by
  have equality :=
    (Algebra.GrothendieckAddGroup.lift (M := EffectiveDivisor F)
      (G := ExplicitDivisor F)).symm_apply_apply effectiveToExplicit
  exact DFunLike.congr_fun equality x

/-- The nonnegativity predicate on the explicit divisor group, coordinatewise. -/
def explicitNonneg (v : ExplicitDivisor F) : Prop :=
  (∀ s : HeightOneSpectrum (𝓞 F), 0 ≤ v.1 s) ∧
    ∀ w : NumberField.InfinitePlace F, 0 ≤ v.2 w

/-- Addition of explicit divisors preserves nonnegativity. -/
theorem explicitNonneg_add {a b : ExplicitDivisor F}
    (ha : explicitNonneg a) (hb : explicitNonneg b) :
    explicitNonneg (a + b) := by
  refine ⟨fun s => ?_, fun w => ?_⟩
  · rw [show (a + b).1 = a.1 + b.1 from rfl, Finsupp.add_apply]
    exact add_nonneg (ha.1 s) (hb.1 s)
  · rw [show (a + b).2 = a.2 + b.2 from rfl, Pi.add_apply]
    exact add_nonneg (ha.2 w) (hb.2 w)

/-- Nonnegativity descends along positive natural multiples. -/
theorem explicitNonneg_of_nsmul {n : ℕ} (hn : 0 < n) {v : ExplicitDivisor F}
    (h : explicitNonneg (n • v)) : explicitNonneg v := by
  refine ⟨fun s => ?_, fun w => ?_⟩
  · have hs : (0 : ℤ) ≤ n • v.1 s := by
      have h' := h.1 s
      rwa [Prod.smul_fst, Finsupp.nsmul_apply] at h'
    exact (nsmul_nonneg_iff (Nat.ne_of_gt hn)).mp hs
  · have hw : (0 : ℝ) ≤ n • v.2 w := by
      have h' := h.2 w
      rwa [Prod.smul_snd, Pi.smul_apply] at h'
    exact (nsmul_nonneg_iff (Nat.ne_of_gt hn)).mp hw

/-! ## 3. The group completion of the effective cone -/

/-- Coordinates of the inclusion on finite places. -/
@[simp]
theorem effectiveToExplicit_fst_apply (m : EffectiveDivisor F)
    (v : HeightOneSpectrum (𝓞 F)) :
    (effectiveToExplicit m).1 v = (m.1 v : ℤ) := by
  simp [effectiveToExplicit, Finsupp.mapRange_apply]

/-- Coordinates of the inclusion on archimedean places. -/
@[simp]
theorem effectiveToExplicit_snd_apply (m : EffectiveDivisor F)
    (w : NumberField.InfinitePlace F) :
    (effectiveToExplicit m).2 w = (m.2 w : ℝ) := rfl

/-- The inclusion of the effective cone lands in the nonnegative part. -/
theorem effectiveToExplicit_nonneg (m : EffectiveDivisor F) :
    explicitNonneg (effectiveToExplicit m) := by
  exact ⟨fun v => by rw [effectiveToExplicit_fst_apply]; exact Int.natCast_nonneg _,
    fun w => by rw [effectiveToExplicit_snd_apply]; exact NNReal.coe_nonneg _⟩

/-- The inclusion of the effective cone into the explicit divisor group is
injective. -/
theorem effectiveToExplicit_injective :
    Function.Injective (effectiveToExplicit (F := F)) := by
  intro a b h
  have hfin := congrArg Prod.fst h
  have hinf := congrArg Prod.snd h
  apply Prod.ext
  · ext v
    have hv := congrArg (fun g : HeightOneSpectrum (𝓞 F) →₀ ℤ => g v) hfin
    change (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) a.1) v =
      (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) b.1) v at hv
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply] at hv
    exact_mod_cast hv
  · funext w
    have hw := congrArg (fun g : NumberField.InfinitePlace F → ℝ => g w) hinf
    exact NNReal.coe_injective hw

/-- Representative computation in the group completion: the class of a pair
(a, s) plus the class of s is the class of a. -/
theorem cone_mk_add_of (a : EffectiveDivisor F)
    (s : (⊤ : AddSubmonoid (EffectiveDivisor F))) :
    AddLocalization.mk a s + Algebra.GrothendieckAddGroup.of s.1 =
      Algebra.GrothendieckAddGroup.of a := by
  change AddLocalization.mk a s +
      AddLocalization.mk s.1 (0 : (⊤ : AddSubmonoid (EffectiveDivisor F))) =
    AddLocalization.mk a (0 : (⊤ : AddSubmonoid (EffectiveDivisor F)))
  rw [AddLocalization.mk_add]
  apply AddLocalization.mk_eq_mk_iff.mpr
  rw [AddLocalization.r_iff_exists]
  refine ⟨0, ?_⟩
  simp only [AddSubmonoid.coe_zero, zero_add, add_zero]
  abel

/-- The comparison map on a localization representative is the difference of the
inclusions. -/
theorem coneComparison_mk (a : EffectiveDivisor F)
    (s : (⊤ : AddSubmonoid (EffectiveDivisor F))) :
    coneComparison (AddLocalization.mk a s) =
      effectiveToExplicit a - effectiveToExplicit s.1 := by
  have h := congrArg coneComparison (cone_mk_add_of (F := F) a s)
  rw [map_add, coneComparison_of, coneComparison_of] at h
  exact eq_sub_of_add_eq h
/-! ## 4. The range of the inclusion and the group completion -/

/-- The range of the canonical inclusion of the effective cone consists exactly
of the nonnegative explicit divisors. -/
theorem coneComparison_nonneg_iff_mem_range
    (x : Algebra.GrothendieckAddGroup (EffectiveDivisor F)) :
    x ∈ Set.range (Algebra.GrothendieckAddGroup.of (M := EffectiveDivisor F)) ↔
      explicitNonneg (coneComparison x) := by
  constructor
  · rintro ⟨m, rfl⟩
    rw [coneComparison_of]
    exact effectiveToExplicit_nonneg m
  · intro hx
    revert hx
    refine AddLocalization.ind (p := fun x =>
      explicitNonneg (coneComparison x) →
        x ∈ Set.range (Algebra.GrothendieckAddGroup.of (M := EffectiveDivisor F))) ?_ x
    intro y hy
    rw [coneComparison_mk] at hy
    have hfin_le : ∀ v : HeightOneSpectrum (𝓞 F), y.2.1.1 v ≤ y.1.1 v := by
      intro v
      have hv := hy.1 v
      change (0 : ℤ) ≤ (effectiveToExplicit y.1).1 v -
        (effectiveToExplicit y.2.1).1 v at hv
      rw [effectiveToExplicit_fst_apply, effectiveToExplicit_fst_apply] at hv
      have hv' : (y.2.1.1 v : ℤ) ≤ (y.1.1 v : ℤ) := by omega
      exact_mod_cast hv'
    have hinf_le : ∀ w : NumberField.InfinitePlace F, y.2.1.2 w ≤ y.1.2 w := by
      intro w
      have hw := hy.2 w
      change (0 : ℝ) ≤ (effectiveToExplicit y.1).2 w -
        (effectiveToExplicit y.2.1).2 w at hw
      rw [effectiveToExplicit_snd_apply, effectiveToExplicit_snd_apply] at hw
      apply NNReal.coe_le_coe.mp
      linarith
    have hf_e : ∀ v : HeightOneSpectrum (𝓞 F),
        y.1.1 v - y.2.1.1 v ≠ 0 → v ∈ y.1.1.support := by
      intro v hv
      by_contra hmem
      have ha0 : y.1.1 v = 0 := by
        rw [Finsupp.mem_support_iff] at hmem
        exact not_not.mp hmem
      have hs0 : y.2.1.1 v = 0 := by
        have := hfin_le v
        omega
      simpa [ha0, hs0] using hv
    let e : EffectiveDivisor F :=
      (Finsupp.onFinset y.1.1.support (fun v => y.1.1 v - y.2.1.1 v) hf_e,
        fun w => y.1.2 w - y.2.1.2 w)
    have hsum : y.2.1 + e = y.1 := by
      apply Prod.ext
      · ext v
        change y.2.1.1 v +
          (Finsupp.onFinset y.1.1.support (fun v => y.1.1 v - y.2.1.1 v) hf_e) v =
            y.1.1 v
        rw [Finsupp.onFinset_apply]
        have hle := hfin_le v
        omega
      · funext w
        change y.2.1.2 w + (y.1.2 w - y.2.1.2 w) = y.1.2 w
        exact add_tsub_cancel_of_le (hinf_le w)
    have hclass : AddLocalization.mk y.1 y.2 = Algebra.GrothendieckAddGroup.of e := by
      have h1 := cone_mk_add_of (F := F) y.1 y.2
      have h2 : Algebra.GrothendieckAddGroup.of y.1 =
          Algebra.GrothendieckAddGroup.of y.2.1 +
            Algebra.GrothendieckAddGroup.of e := by
        rw [← hsum, map_add]
      have h3 : AddLocalization.mk y.1 y.2 +
          Algebra.GrothendieckAddGroup.of y.2.1 =
          Algebra.GrothendieckAddGroup.of e +
            Algebra.GrothendieckAddGroup.of y.2.1 := by
        rw [h1, h2, add_comm]
      exact add_right_cancel h3
    exact ⟨e, hclass.symm⟩

/-- The comparison map is injective. -/
theorem coneComparison_injective : Function.Injective (coneComparison (F := F)) := by
  intro x y hxy
  have hdiff : coneComparison (F := F) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnonneg : explicitNonneg (coneComparison (F := F) (x - y)) := by
    rw [hdiff]
    exact ⟨fun _ => le_refl 0, fun _ => le_refl 0⟩
  obtain ⟨e, he⟩ :=
    (coneComparison_nonneg_iff_mem_range (F := F) (x - y)).mpr hnonneg
  have hee : e = 0 := by
    apply effectiveToExplicit_injective
    rw [map_zero]
    rw [← coneComparison_of, he, hdiff]
  have hzero : x - y = 0 := by
    rw [← he, hee, map_zero]
  exact sub_eq_zero.mp hzero

/-- The comparison map is surjective. -/
theorem coneComparison_surjective : Function.Surjective (coneComparison (F := F)) := by
  intro v
  let a : EffectiveDivisor F :=
    (Finsupp.onFinset v.1.support (fun s => (v.1 s).toNat) (by
        intro s hs
        by_contra hmem
        have h0 : v.1 s = 0 := by simpa [Finsupp.mem_support_iff] using hmem
        exact hs (by simp [h0])),
      fun w => (v.2 w).toNNReal)
  let b : EffectiveDivisor F :=
    (Finsupp.onFinset v.1.support (fun s => (-v.1 s).toNat) (by
        intro s hs
        by_contra hmem
        have h0 : v.1 s = 0 := by simpa [Finsupp.mem_support_iff] using hmem
        have h0' : -v.1 s = 0 := by rw [h0]; rfl
        exact hs (by simp [h0'])),
      fun w => (-v.2 w).toNNReal)
  refine ⟨Algebra.GrothendieckAddGroup.of a -
    Algebra.GrothendieckAddGroup.of b, ?_⟩
  rw [map_sub, coneComparison_of, coneComparison_of]
  apply Prod.ext
  · ext s
    change (effectiveToExplicit a).1 s - (effectiveToExplicit b).1 s = v.1 s
    rw [effectiveToExplicit_fst_apply, effectiveToExplicit_fst_apply]
    change ((v.1 s).toNat : ℤ) - (((-v.1 s).toNat) : ℤ) = v.1 s
    rcases le_total (0 : ℤ) (v.1 s) with h | h
    · rw [Int.toNat_of_nonneg h, Int.toNat_of_nonpos (by omega)]
      omega
    · rw [Int.toNat_of_nonpos h, Int.toNat_of_nonneg (by omega)]
      omega
  · funext w
    change (effectiveToExplicit a).2 w - (effectiveToExplicit b).2 w = v.2 w
    rw [effectiveToExplicit_snd_apply, effectiveToExplicit_snd_apply]
    change ((v.2 w).toNNReal : ℝ) - ((-v.2 w).toNNReal : ℝ) = v.2 w
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    rcases le_total 0 (v.2 w) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring

/-- The group completion of the effective cone is the explicit divisor group. -/
def coneGrothendieckEquiv :
    Algebra.GrothendieckAddGroup (EffectiveDivisor F) ≃+ ExplicitDivisor F :=
  AddEquiv.ofBijective (coneComparison (F := F))
    ⟨coneComparison_injective, coneComparison_surjective⟩

/-- The group completion equivalence is the comparison map. -/
@[simp]
theorem coneGrothendieckEquiv_apply
    (x : Algebra.GrothendieckAddGroup (EffectiveDivisor F)) :
    coneGrothendieckEquiv x = coneComparison x := rfl

/-- The group completion equivalence extends the inclusion of the cone. -/
@[simp]
theorem coneGrothendieckEquiv_of (x : EffectiveDivisor F) :
    coneGrothendieckEquiv (Algebra.GrothendieckAddGroup.of x) =
      effectiveToExplicit x :=
  coneComparison_of x

/-! ## 5. The divisorial monoid and its functorial layers -/

/-- The effective divisor cone is a sharp, integral, saturated divisorial monoid:
the divisorial case of Frobenioids I, Definition 1.1(i). -/
def effectiveDivisorialAddMonoid : Iut.DivisorialAddMonoid where
  carrier := EffectiveDivisor F
  integral := effectiveDivisor_add_left_cancel
  sharp := effectiveDivisor_sharp
  saturated := by
    intro x n hx
    have hx' : explicitNonneg (n.1 • coneComparison (F := F) x) := by
      rw [← map_nsmul]
      obtain ⟨m, hm⟩ := hx
      rw [← hm, coneComparison_of]
      exact effectiveToExplicit_nonneg m
    exact (coneComparison_nonneg_iff_mem_range (F := F) x).mpr
      (explicitNonneg_of_nsmul n.2 hx')

/-- The single-fibre divisorial monoid of the model carrier over the bottom base
category: the effective divisor cone with identity pullbacks. -/
def globalDivisorMonoidOn :
    Iut.DivisorialMonoidOn BottomBase BottomFSM where
  obj _ := effectiveDivisorialAddMonoid (F := F)
  pullback _ := AddMonoidHom.id (EffectiveDivisor F)
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  characteristicallyInjective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id

/-- The rational-function monoid of the model carrier: the global units F^! on
the single object, with identity pullbacks. -/
def globalRationalFunctions :
    Iut.SourceModelFrobenioid.GroupLikeAddMonoidOn BottomBase BottomFSM where
  obj _ := Additive Fˣ
  addCommGroup _ := inferInstance
  pullback _ := AddMonoidHom.id (Additive Fˣ)
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  pullback_injective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id

/-! ## 6. The principal divisor and the model input -/

/-- The principal divisor of a global unit in explicit coordinates: finitely
supported finite-place exponents nu_v(f) and archimedean coordinates -log(w f). -/
def principalDivisorExplicit : Additive Fˣ →+ ExplicitDivisor F where
  toFun u :=
    (principalDivisorFinite u.toMul, fun w => principalDivisorInfinite u.toMul w)
  map_zero' := by
    apply Prod.ext
    · change principalDivisorFinite ((0 : Additive Fˣ).toMul) = 0
      rw [toMul_zero, principalDivisorFinite_one]
    · funext w
      change principalDivisorInfinite ((0 : Additive Fˣ).toMul) w = 0
      rw [toMul_zero]
      simp [principalDivisorInfinite]
  map_add' := by
    intro u v
    apply Prod.ext
    · change principalDivisorFinite (Additive.toMul (u + v)) =
        principalDivisorFinite (Additive.toMul u) +
          principalDivisorFinite (Additive.toMul v)
      rw [toMul_add, principalDivisorFinite_mul]
    · funext w
      change principalDivisorInfinite (Additive.toMul (u + v)) w =
        principalDivisorInfinite (Additive.toMul u) w +
          principalDivisorInfinite (Additive.toMul v) w
      rw [toMul_add, principalDivisorInfinite_mul]
      rfl

/-- The principal divisor map of the model Frobenioid, into the Grothendieck
group of the effective cone. -/
def globalModelDivisor :
    Additive Fˣ →+ Algebra.GrothendieckAddGroup (EffectiveDivisor F) :=
  coneGrothendieckEquiv.symm.toAddMonoidHom.comp principalDivisorExplicit

/-- The actual model-Frobenioid input attached to the number field F. -/
def numberFieldSourceModelInput :
    Iut.SourceModelFrobenioid.Input (globalDivisorMonoidOn (F := F)) where
  rationalFunctions := globalRationalFunctions (F := F)
  divisor X := by
    change Additive Fˣ →+ Algebra.GrothendieckAddGroup (EffectiveDivisor F)
    exact globalModelDivisor (F := F)
  divisor_natural := by
    intro X Y f value
    have hXY : X = Y := Subsingleton.elim X Y
    subst Y
    have hf : f = 𝟙 X := bottomBase_hom_eq_id f
    rw [hf]
    change globalModelDivisor (F := F) value =
      (Iut.DivisorialMonoidOn.gpPullback (globalDivisorMonoidOn (F := F)) (𝟙 X))
        (globalModelDivisor (F := F) value)
    rw [Iut.DivisorialMonoidOn.gpPullback_id]
    rfl

/-- The global Example 3.6(ii) Frobenioid presentation attached to the
number-field model input. -/
noncomputable def numberFieldFrobenioidPresentation
    (F : Type u) [Field F] [NumberField F] :
    Iut.FrobenioidPresentation :=
  Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation
    (D := BottomBase) (IsFSM := BottomFSM)
    (Phi := globalDivisorMonoidOn (F := F))
    (data := numberFieldSourceModelInput (F := F))
    (fun f => bottomBase_arrow_epi f)

/-! ## 7. The backend object dictionary with the global ideal families -/

/-- The divisor class of a global ideal family in the model carrier:
d(J) = -delta(J) = (-J.finite, fun w => -J.infinite w). -/
def idealFamilyDivisorClass (J : GlobalIdealFamily F) :
    Algebra.GrothendieckAddGroup (EffectiveDivisor F) :=
  coneGrothendieckEquiv.symm (-J.finite, fun w => -J.infinite w)

/-- The model object attached to a global ideal family: base the unique object of
the bottom base category and divisor class d(J) = -delta(J). -/
def objectOfIdealFamily (J : GlobalIdealFamily F) :
    Iut.SourceModelFrobenioid.Object (globalDivisorMonoidOn (F := F)) where
  base := bottomPoint
  divisorClass := idealFamilyDivisorClass (F := F) J



end SourceModelBackend
end Example36
end LeanFormal.IUT.IUTII.Frobenioid
end
