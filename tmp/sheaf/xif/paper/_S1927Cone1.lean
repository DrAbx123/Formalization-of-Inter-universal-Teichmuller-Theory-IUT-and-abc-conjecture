import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import Mathlib.Data.NNReal.Basic

noncomputable section
open CategoryTheory IsDedekindDomain NumberField
open scoped BigOperators

namespace S1927Real

open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend

universe u

variable {F : Type u} [Field F] [NumberField F]

abbrev RealEffectiveDivisor : Type u :=
  (HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ NNReal) ×
    (NumberField.InfinitePlace F → NNReal)

abbrev RealExplicitDivisor : Type u :=
  (HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ Real) ×
    (NumberField.InfinitePlace F → Real)

theorem realEffectiveDivisor_add_left_cancel (a b c : RealEffectiveDivisor (F := F))
    (h : a + b = a + c) : b = c := by
  have hfin : a.1 + b.1 = a.1 + c.1 := congrArg Prod.fst h
  have hinf : a.2 + b.2 = a.2 + c.2 := congrArg Prod.snd h
  apply Prod.ext
  · apply Finsupp.ext
    intro v
    have hv := congrArg (fun g : HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ NNReal => g v) hfin
    simp only [Finsupp.add_apply] at hv
    exact add_left_cancel (a := a.1 v) hv
  · funext w
    have hw := congrFun hinf w
    simp only [Pi.add_apply] at hw
    exact add_left_cancel (a := a.2 w) hw

theorem realEffectiveDivisor_add_right_cancel (a b c : RealEffectiveDivisor (F := F))
    (h : a + b = c + b) : a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact realEffectiveDivisor_add_left_cancel b a c h

theorem realEffectiveDivisor_sharp (a : RealEffectiveDivisor (F := F))
    (h : IsAddUnit a) : a = 0 := by
  obtain ⟨b, hb⟩ := h.exists_neg
  have hfin : a.1 + b.1 = 0 := congrArg Prod.fst hb
  have hinf : a.2 + b.2 = 0 := congrArg Prod.snd hb
  apply Prod.ext
  · apply Finsupp.ext
    intro v
    have hv := congrArg (fun g : HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ NNReal => g v) hfin
    simp only [Finsupp.add_apply, Finsupp.zero_apply] at hv
    have hle : a.1 v ≤ 0 := by
      have h' : a.1 v ≤ a.1 v + b.1 v := le_add_right le_rfl
      rwa [hv] at h'
    exact le_antisymm hle (zero_le : (0 : NNReal) ≤ a.1 v)
  · funext w
    have hw := congrFun hinf w
    simp only [Pi.add_apply, Pi.zero_apply] at hw
    have hle : a.2 w ≤ 0 := by
      have h' : a.2 w ≤ a.2 w + b.2 w := le_add_right le_rfl
      rwa [hw] at h'
    exact le_antisymm hle (zero_le : (0 : NNReal) ≤ a.2 w)

def realEffectiveToExplicit : RealEffectiveDivisor (F := F) →+ RealExplicitDivisor (F := F) where
  toFun d :=
    (d.1.mapRange (fun n : NNReal => (n : Real)) (by simp),
      fun w => (d.2 w : Real))
  map_zero' := by
    apply Prod.ext
    · exact Finsupp.mapRange_zero (f := fun n : NNReal => (n : Real)) (hf := by simp)
    · funext w
      simp
  map_add' := by
    intro a b
    apply Prod.ext
    · change Finsupp.mapRange (fun n : NNReal => (n : Real)) (by simp) (a.1 + b.1) =
        Finsupp.mapRange (fun n : NNReal => (n : Real)) (by simp) a.1 +
          Finsupp.mapRange (fun n : NNReal => (n : Real)) (by simp) b.1
      rw [Finsupp.mapRange_add (fun x y => NNReal.coe_add x y)]
    · funext w
      simp only [Prod.snd_add, Pi.add_apply, NNReal.coe_add]

def realConeComparison :
    Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := F)) →+ RealExplicitDivisor (F := F) :=
  Algebra.GrothendieckAddGroup.lift (realEffectiveToExplicit (F := F))

@[simp]
theorem realConeComparison_of (x : RealEffectiveDivisor (F := F)) :
    realConeComparison (Algebra.GrothendieckAddGroup.of x) =
      realEffectiveToExplicit x := by
  have equality :=
    (Algebra.GrothendieckAddGroup.lift (M := RealEffectiveDivisor (F := F))
      (G := RealExplicitDivisor (F := F))).symm_apply_apply (realEffectiveToExplicit (F := F))
  exact DFunLike.congr_fun equality x

def realExplicitNonneg (v : RealExplicitDivisor (F := F)) : Prop :=
  (∀ s : HeightOneSpectrum (NumberField.RingOfIntegers F), 0 ≤ v.1 s) ∧
    ∀ w : NumberField.InfinitePlace F, 0 ≤ v.2 w

theorem realExplicitNonneg_add {a b : RealExplicitDivisor (F := F)}
    (ha : realExplicitNonneg a) (hb : realExplicitNonneg b) :
    realExplicitNonneg (a + b) := by
  refine ⟨fun s => ?_, fun w => ?_⟩
  · rw [show (a + b).1 = a.1 + b.1 from rfl, Finsupp.add_apply]
    exact add_nonneg (ha.1 s) (hb.1 s)
  · rw [show (a + b).2 = a.2 + b.2 from rfl, Pi.add_apply]
    exact add_nonneg (ha.2 w) (hb.2 w)

theorem realExplicitNonneg_of_nsmul {n : Nat} (hn : 0 < n) {v : RealExplicitDivisor (F := F)}
    (h : realExplicitNonneg (n • v)) : realExplicitNonneg v := by
  refine ⟨fun s => ?_, fun w => ?_⟩
  · have hs : (0 : Real) ≤ n • v.1 s := by
      have h' := h.1 s
      rwa [Prod.smul_fst, Finsupp.nsmul_apply] at h'
    exact (nsmul_nonneg_iff (Nat.ne_of_gt hn)).mp hs
  · have hw : (0 : Real) ≤ n • v.2 w := by
      have h' := h.2 w
      rwa [Prod.smul_snd, Pi.smul_apply] at h'
    exact (nsmul_nonneg_iff (Nat.ne_of_gt hn)).mp hw

@[simp]
theorem realEffectiveToExplicit_fst_apply (m : RealEffectiveDivisor (F := F))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (realEffectiveToExplicit m).1 v = (m.1 v : Real) := by
  simp [realEffectiveToExplicit, Finsupp.mapRange_apply]

@[simp]
theorem realEffectiveToExplicit_snd_apply (m : RealEffectiveDivisor (F := F))
    (w : NumberField.InfinitePlace F) :
    (realEffectiveToExplicit m).2 w = (m.2 w : Real) := rfl

theorem realEffectiveToExplicit_nonneg (m : RealEffectiveDivisor (F := F)) :
    realExplicitNonneg (realEffectiveToExplicit m) := by
  exact ⟨fun v => by rw [realEffectiveToExplicit_fst_apply]; exact NNReal.coe_nonneg _,
    fun w => by rw [realEffectiveToExplicit_snd_apply]; exact NNReal.coe_nonneg _⟩

theorem realEffectiveToExplicit_injective :
    Function.Injective (realEffectiveToExplicit (F := F)) := by
  intro a b h
  have hfin := congrArg Prod.fst h
  have hinf := congrArg Prod.snd h
  apply Prod.ext
  · ext v
    have hv := congrArg (fun g : HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ Real => g v) hfin
    change (Finsupp.mapRange (fun n : NNReal => (n : Real)) (by simp) a.1) v =
      (Finsupp.mapRange (fun n : NNReal => (n : Real)) (by simp) b.1) v at hv
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply] at hv
    exact hv
  · funext w
    have hw := congrArg (fun g : NumberField.InfinitePlace F → Real => g w) hinf
    exact NNReal.coe_injective hw

theorem realCone_mk_add_of (a : RealEffectiveDivisor (F := F))
    (s : (⊤ : AddSubmonoid (RealEffectiveDivisor (F := F)))) :
    AddLocalization.mk a s + Algebra.GrothendieckAddGroup.of s.1 =
      Algebra.GrothendieckAddGroup.of a := by
  change AddLocalization.mk a s +
      AddLocalization.mk s.1 (0 : (⊤ : AddSubmonoid (RealEffectiveDivisor (F := F)))) =
    AddLocalization.mk a (0 : (⊤ : AddSubmonoid (RealEffectiveDivisor (F := F))))
  rw [AddLocalization.mk_add]
  apply AddLocalization.mk_eq_mk_iff.mpr
  rw [AddLocalization.r_iff_exists]
  refine ⟨0, ?_⟩
  simp only [AddSubmonoid.coe_zero, zero_add, add_zero]
  abel

theorem realConeComparison_mk (a : RealEffectiveDivisor (F := F))
    (s : (⊤ : AddSubmonoid (RealEffectiveDivisor (F := F)))) :
    realConeComparison (AddLocalization.mk a s) =
      realEffectiveToExplicit a - realEffectiveToExplicit s.1 := by
  have h := congrArg realConeComparison (realCone_mk_add_of (F := F) a s)
  rw [map_add, realConeComparison_of, realConeComparison_of] at h
  exact eq_sub_of_add_eq h

theorem realConeComparison_nonneg_iff_mem_range
    (x : Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := F))) :
    x ∈ Set.range (Algebra.GrothendieckAddGroup.of (M := RealEffectiveDivisor (F := F))) ↔
      realExplicitNonneg (realConeComparison (F := F) x) := by
  constructor
  · rintro ⟨m, rfl⟩
    rw [realConeComparison_of]
    exact realEffectiveToExplicit_nonneg m
  · intro hx
    revert hx
    refine AddLocalization.ind (p := fun x =>
      realExplicitNonneg (realConeComparison (F := F) x) →
        x ∈ Set.range (Algebra.GrothendieckAddGroup.of
          (M := RealEffectiveDivisor (F := F)))) ?_ x
    intro y hy
    rw [realConeComparison_mk] at hy
    have hfin_le : ∀ v, y.2.1.1 v ≤ y.1.1 v := by
      intro v
      have hv := hy.1 v
      change (0 : Real) ≤ (realEffectiveToExplicit y.1).1 v -
        (realEffectiveToExplicit y.2.1).1 v at hv
      rw [realEffectiveToExplicit_fst_apply, realEffectiveToExplicit_fst_apply] at hv
      exact NNReal.coe_le_coe.mp (sub_nonneg.mp hv)
    have hinf_le : ∀ w, y.2.1.2 w ≤ y.1.2 w := by
      intro w
      have hw := hy.2 w
      change (0 : Real) ≤ (realEffectiveToExplicit y.1).2 w -
        (realEffectiveToExplicit y.2.1).2 w at hw
      rw [realEffectiveToExplicit_snd_apply, realEffectiveToExplicit_snd_apply] at hw
      exact NNReal.coe_le_coe.mp (sub_nonneg.mp hw)
    have hf_e : ∀ v, y.1.1 v - y.2.1.1 v ≠ 0 → v ∈ y.1.1.support := by
      intro v hv
      by_contra hmem
      rw [Finsupp.mem_support_iff] at hmem
      have ha0 : y.1.1 v = 0 := not_not.mp hmem
      have hs0 : y.2.1.1 v = 0 := by
        have := hfin_le v
        rw [ha0] at this
        exact le_antisymm this zero_le
      exact hv (by rw [ha0, hs0]; simp)
    let e : RealEffectiveDivisor (F := F) :=
      (Finsupp.onFinset y.1.1.support (fun v => y.1.1 v - y.2.1.1 v) hf_e,
        fun w => y.1.2 w - y.2.1.2 w)
    have hsum : y.2.1 + e = y.1 := by
      apply Prod.ext
      · apply Finsupp.ext
        intro v
        change y.2.1.1 v + (y.1.1 v - y.2.1.1 v) = y.1.1 v
        exact add_tsub_cancel_of_le (hfin_le v)
      · funext w
        change y.2.1.2 w + (y.1.2 w - y.2.1.2 w) = y.1.2 w
        exact add_tsub_cancel_of_le (hinf_le w)
    have hclass : AddLocalization.mk y.1 y.2 =
        Algebra.GrothendieckAddGroup.of e := by
      have h1 := realCone_mk_add_of (F := F) y.1 y.2
      have h2 : Algebra.GrothendieckAddGroup.of y.1 =
          Algebra.GrothendieckAddGroup.of y.2.1 + Algebra.GrothendieckAddGroup.of e := by
        rw [← hsum, map_add]
      have h3 : AddLocalization.mk y.1 y.2 + Algebra.GrothendieckAddGroup.of y.2.1 =
          Algebra.GrothendieckAddGroup.of e + Algebra.GrothendieckAddGroup.of y.2.1 := by
        rw [h1, h2, add_comm]
      exact add_right_cancel h3
    exact ⟨e, hclass.symm⟩

theorem realConeComparison_injective :
    Function.Injective (realConeComparison (F := F)) := by
  intro x y hxy
  have hdiff : realConeComparison (F := F) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnonneg : realExplicitNonneg (realConeComparison (F := F) (x - y)) := by
    rw [hdiff]
    exact ⟨fun _ => le_refl 0, fun _ => le_refl 0⟩
  obtain ⟨e, he⟩ :=
    (realConeComparison_nonneg_iff_mem_range (F := F) (x - y)).mpr hnonneg
  have hee : e = 0 := by
    apply realEffectiveToExplicit_injective
    rw [map_zero]
    rw [← realConeComparison_of, he, hdiff]
  have hzero : x - y = 0 := by
    rw [← he, hee, map_zero]
  exact sub_eq_zero.mp hzero

theorem realConeComparison_surjective :
    Function.Surjective (realConeComparison (F := F)) := by
  intro v
  let a : RealEffectiveDivisor (F := F) :=
    (Finsupp.onFinset v.1.support (fun s => (v.1 s).toNNReal) (by
        intro s hs
        by_contra hmem
        have h0 : v.1 s = 0 := by simpa [Finsupp.mem_support_iff] using hmem
        exact hs (by simp [h0])),
      fun w => (v.2 w).toNNReal)
  let b : RealEffectiveDivisor (F := F) :=
    (Finsupp.onFinset v.1.support (fun s => (-v.1 s).toNNReal) (by
        intro s hs
        by_contra hmem
        have h0 : v.1 s = 0 := by simpa [Finsupp.mem_support_iff] using hmem
        have h0' : -v.1 s = 0 := by simp [h0]
        exact hs (by simp [h0'])),
      fun w => (-v.2 w).toNNReal)
  refine ⟨Algebra.GrothendieckAddGroup.of a - Algebra.GrothendieckAddGroup.of b, ?_⟩
  rw [map_sub, realConeComparison_of, realConeComparison_of]
  apply Prod.ext
  · apply Finsupp.ext
    intro s
    change (realEffectiveToExplicit a).1 s - (realEffectiveToExplicit b).1 s = v.1 s
    rw [realEffectiveToExplicit_fst_apply, realEffectiveToExplicit_fst_apply]
    change ((v.1 s).toNNReal : Real) - (((-v.1 s).toNNReal : Real)) = v.1 s
    rcases le_total (0 : Real) (v.1 s) with h | h
    · rw [Real.coe_toNNReal', Real.coe_toNNReal']
      rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [Real.coe_toNNReal', Real.coe_toNNReal']
      rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  · funext w
    change (realEffectiveToExplicit a).2 w - (realEffectiveToExplicit b).2 w = v.2 w
    rw [realEffectiveToExplicit_snd_apply, realEffectiveToExplicit_snd_apply]
    change ((v.2 w).toNNReal : Real) - (((-v.2 w).toNNReal : Real)) = v.2 w
    rcases le_total (0 : Real) (v.2 w) with h | h
    · rw [Real.coe_toNNReal', Real.coe_toNNReal']
      rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [Real.coe_toNNReal', Real.coe_toNNReal']
      rw [max_eq_right h, max_eq_left (by linarith)]
      ring

def realConeGrothendieckEquiv :
    Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := F)) ≃+ RealExplicitDivisor (F := F) :=
  AddEquiv.ofBijective (realConeComparison (F := F))
    ⟨realConeComparison_injective (F := F), realConeComparison_surjective (F := F)⟩

@[simp]
theorem realConeGrothendieckEquiv_apply
    (x : Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := F))) :
    realConeGrothendieckEquiv x = realConeComparison (F := F) x := rfl

@[simp]
theorem realConeGrothendieckEquiv_of (x : RealEffectiveDivisor (F := F)) :
    realConeGrothendieckEquiv (Algebra.GrothendieckAddGroup.of x) =
      realEffectiveToExplicit x :=
  realConeComparison_of x

theorem realEffectiveDivisor_saturated
    (x : Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := F))) (n : PNat) :
    n.1 • x ∈ Set.range (Algebra.GrothendieckAddGroup.of
      (M := RealEffectiveDivisor (F := F))) →
      x ∈ Set.range (Algebra.GrothendieckAddGroup.of
        (M := RealEffectiveDivisor (F := F))) := by
  intro hx
  have hx' : realExplicitNonneg (n.1 • realConeComparison (F := F) x) := by
    rw [← map_nsmul]
    obtain ⟨m, hm⟩ := hx
    rw [← hm, realConeComparison_of]
    exact realEffectiveToExplicit_nonneg m
  exact (realConeComparison_nonneg_iff_mem_range (F := F) x).mpr
    ((realExplicitNonneg_of_nsmul (F := F) n.2) hx')


def effectiveRealDivisorialAddMonoid (F : Type u) [Field F] [NumberField F] : Iut.DivisorialAddMonoid where
  carrier := RealEffectiveDivisor (F := F)
  integral := realEffectiveDivisor_add_left_cancel
  sharp := realEffectiveDivisor_sharp
  saturated := realEffectiveDivisor_saturated

def globalDivisorMonoidOnReal (F : Type u) [Field F] [NumberField F] :
    Iut.DivisorialMonoidOn BottomBase BottomFSM where
  obj _ := effectiveRealDivisorialAddMonoid (F := F)
  pullback _ := AddMonoidHom.id (RealEffectiveDivisor (F := F))
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  characteristicallyInjective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id

def intToRealExplicit :
    ((HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ Int) ×
      (NumberField.InfinitePlace F → Real)) →+
      RealExplicitDivisor (F := F) where
  toFun v :=
    (v.1.mapRange (fun z : Int => (z : Real)) (by simp), v.2)
  map_zero' := by
    apply Prod.ext
    · exact Finsupp.mapRange_zero (f := fun z : Int => (z : Real)) (hf := by simp)
    · rfl
  map_add' := by
    intro a b
    apply Prod.ext
    · change Finsupp.mapRange (fun z : Int => (z : Real)) (by simp) (a.1 + b.1) =
        Finsupp.mapRange (fun z : Int => (z : Real)) (by simp) a.1 +
          Finsupp.mapRange (fun z : Int => (z : Real)) (by simp) b.1
      rw [Finsupp.mapRange_add (fun x y => Int.cast_add x y)]
    · rfl

def realPrincipalDivisor : Additive Fˣ →+ RealExplicitDivisor (F := F) :=
  (intToRealExplicit (F := F)).comp (principalDivisorExplicit (F := F))

def realBirationalSubmodule : AddSubgroup (RealExplicitDivisor (F := F)) :=
  (Submodule.span Real (Set.range (realPrincipalDivisor (F := F)))).toAddSubgroup

def realGlobalRationalFunctions (F : Type u) [Field F] [NumberField F] :
    Iut.SourceModelFrobenioid.GroupLikeAddMonoidOn BottomBase BottomFSM where
  obj _ := realBirationalSubmodule (F := F)
  addCommGroup _ := inferInstance
  pullback _ := AddMonoidHom.id (realBirationalSubmodule (F := F))
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  pullback_injective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id

def numberFieldSourceModelInputRealified (F : Type u) [Field F] [NumberField F] :
    Iut.SourceModelFrobenioid.Input (globalDivisorMonoidOnReal (F := F)) where
  rationalFunctions := realGlobalRationalFunctions (F := F)
  divisor X := by
    change realBirationalSubmodule (F := F) →+
      Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := F))
    exact (realConeGrothendieckEquiv (F := F)).symm.toAddMonoidHom.comp
      (AddSubgroup.subtype (realBirationalSubmodule (F := F)))
  divisor_natural := by
    intro X Y f value
    have hXY : X = Y := Subsingleton.elim X Y
    subst Y
    have hf : f = 𝟙 X := bottomBase_hom_eq_id f
    rw [hf]
    change (realConeGrothendieckEquiv (F := F)).symm
        (AddSubgroup.subtype (realBirationalSubmodule (F := F)) value) =
      (Iut.DivisorialMonoidOn.gpPullback (globalDivisorMonoidOnReal (F := F)) (𝟙 X))
        ((realConeGrothendieckEquiv (F := F)).symm
          (AddSubgroup.subtype (realBirationalSubmodule (F := F)) value))
    rw [Iut.DivisorialMonoidOn.gpPullback_id]
    rfl

noncomputable def numberFieldFrobenioidPresentationRealified (F : Type u) [Field F] [NumberField F] :
    Iut.FrobenioidPresentation :=
  Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation
    (D := BottomBase) (IsFSM := BottomFSM)
    (Phi := globalDivisorMonoidOnReal (F := F))
    (data := numberFieldSourceModelInputRealified (F := F))
    (fun f => bottomBase_arrow_epi f)

end S1927Real


