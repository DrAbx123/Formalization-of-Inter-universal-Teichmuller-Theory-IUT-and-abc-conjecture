import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import LeanFormal.IUT.Foundations.Arithmetic.NormLog
import Mathlib.Data.NNReal.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# S1927: the global realified Frobenioid C⊩mod and the global log-shell

Layer: **O** (original Theta-link / q-pilot), on the source-faithful
`S1895PaperO` of `S1895OIdentificationsActual`.

## What this file constructs

1. **The global realified Frobenioid C⊩mod.**  IUT I, Example 3.5, (i), writes
   C⊩mod for the realification of the Frobenioid of [FrdI], Example 6.3,
   associated to the number field Fmod with trivial Galois extension.  Its
   divisor monoid ΦC⊩mod is the realification of the effective arithmetic
   divisor monoid; the realification replaces Z≥0 by R≥0 (Frobenioids I,
   Proposition 5.3 and the effect table of the introduction).  The file
   constructs the actual realified effective divisor cone

     (HeightOneSpectrum O_Fmod →₀ R≥0) × (InfinitePlace Fmod → R≥0),

   proves it is a sharp, integral, saturated divisorial monoid, identifies its
   Grothendieck group with the explicit real divisor group

     (HeightOneSpectrum O_Fmod →₀ R) × (InfinitePlace Fmod → R),

   and builds the model Frobenioid presentation of Theorem 5.2 from the actual
   principal divisor map.  The result is a genuine `Iut.FrobenioidPresentation`
   on the one-object/one-arrow base category, not a carrier record and not a
   gate witness.  It is attached to the base field Fmod of the S1895 input by
   `paperGlobalRealifiedFrobenioid`.

2. **The q_v zero-locus divisor.**  For every bad place of the S1895 input, the
   actual base Fmod prime divisor `b.1.maximalIdeal` is put in the realified
   divisor monoid with coefficient one; the global divisor is the finite sum
   over the actual bad places.  This is the literal zero-locus prime divisor
   (support) of the q_v; the q_v valuation order is carried by the actual
   S1487 q-candidate and is not replaced by a fabricated coefficient.

3. **The reduced finite global log-shell/tensor packet.**  At every finite
   prime place of the S1895 one-column, the actual completed local field, its
   units and the norm-log degree give a `SourceLogShellDatum`; the direct-sum
   packet `IQ(sum_v I_v)` and the tensor-packet decomposition are then the
   **reduced** finite global log-shell packet over the one-column index.  This
   uses the existing `SourceLogShellCarrier` reductions: `invariants = top`
   and the norm-log degree.  The actual `G_v`-invariant submonoid and the
   p-adic log are not constructed; they are a separate source gap, not claimed
   here as the paper's global log-shell.

## Exact first missing

The reduced finite log-shell packet is constructed, but the **actual
nonarchimedean `G_v`-invariant log-shell data** (the invariant submonoid and
p-adic log used by `SourceLogShellDatum`) are not; the file uses the existing
reduced carrier (`invariants = top`, norm-log) and does not claim it is the
paper's actual nonarchimedean log-shell.  The **archimedean log-shell datum at
the archimedean places of Fmod** is also not constructed: `SourceLogShellDatum`
is nonarchimedean (it carries a prime p and the (p*_v)^{-1}-scaled
pre-log-shell), while IUT III, Definition 1.1, (ii), gives a distinct
closed-interval/orbit log-shell at the archimedean places.  The type
`S1927FirstMissing` records the exact archimedean missing datum, tied to the
actual completion `w.Completion` and its actual closed unit ball.  The second
gap is the actual four coric vertices (env/gau/LGP/lgp) and the Kummer
evaluation square on them, recorded in `SourceKummerEvaluationArrows` R3; the
reduced square is parameterized by its four strips precisely because the paper
vertices are not constructed.  The full log-Kummer package on 1,circU_Q is
`S1927FullLogKummerUQ`; it is assembled from the constructed finite data and
the named missing inputs.  No Frobenioid, log-shell, Kummer arrow or evaluation
square is fabricated.

## Source locations

* IUT I, Example 3.5, (i) (global realified Frobenioids); [FrdI], Example 6.3
  and Theorem 6.4; [FrdI], Proposition 5.3 (realification).
* IUT III, Definition 3.8, (i) (q-pilot object determined by the q_v);
  IUT III, Theorem 3.11, (ii), (iii), (a), (b) (log-Kummer and evaluation
  square); Definition 1.1, (i), (ii) (log-shells).
* The reduced source interface is `SourceKummerEvaluationArrows` (R3: the
  env/gau/LGP/lgp vertices are not constructed; R6: the q-pilot anchor
  identification is not made).

## Verification

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary inhabitant or
`Nonempty` gate is used.  The missing types are definitions, not inhabited.
-/



noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual

namespace Realified

open CategoryTheory IsDedekindDomain NumberField
open scoped BigOperators


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



end Realified

open Realified
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open IsDedekindDomain NumberField

/-! ## 1. The base field and the global realified Frobenioid C-mod -/

/-- The arithmetic base field Fmod of the S1895 paper input. -/
abbrev PaperFmod (D : S1895PaperInput) : Type :=
  (S1895PaperInput.I D).initial.arithmetic.Fmod

/-- The actual global realified Frobenioid C-mod of S1895PaperO: the
realification of the arithmetic Frobenioid of [FrdI], Example 6.3, over the
actual base field Fmod, built as a model Frobenioid presentation on the
realified effective arithmetic divisor monoid. -/
noncomputable def paperGlobalRealifiedFrobenioid
    (D : S1895PaperInput) : Iut.FrobenioidPresentation :=
  numberFieldFrobenioidPresentationRealified (F := PaperFmod D)

/-- The base object of the presentation is the unique object of the one-object
base category. -/
abbrev paperGlobalBaseObject (D : S1895PaperInput) :
    LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.BottomBase :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.bottomPoint

/-- The divisor monoid of C-mod at its unique base object is the actual
realified effective divisor monoid of Fmod. -/
theorem paperGlobalRealifiedFrobenioid_divisorMonoid
    (D : S1895PaperInput) :
    ((paperGlobalRealifiedFrobenioid D).preFrobenioid.divisorMonoid.obj
      (paperGlobalBaseObject D)).carrier =
      RealEffectiveDivisor (F := PaperFmod D) := rfl

/-- The Grothendieck group of the realified divisor monoid is the explicit real
arithmetic divisor group of Fmod. -/
theorem paperGlobalRealifiedFrobenioid_groupCompletion
    (D : S1895PaperInput) :
    Nonempty (AddEquiv
      (Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := PaperFmod D)))
      (RealExplicitDivisor (F := PaperFmod D))) :=
  ⟨realConeGrothendieckEquiv (F := PaperFmod D)⟩

/-! ## 2. The q_v zero-locus divisor -/

/-- The base Fmod prime of a bad place of the S1895 input. -/
noncomputable def paperBadBasePlace (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    HeightOneSpectrum (NumberField.RingOfIntegers (PaperFmod D)) :=
  b.1.maximalIdeal

/-- The q_v zero-locus prime divisor at a bad base place, as an actual element
of the realified effective divisor monoid.  The coefficient is one: this is the
prime divisor underlying the zero locus.  The q_v order is the actual S1487
candidate order and is not replaced by a fake coefficient. -/
noncomputable def paperQVZeroLocusPrime (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    RealEffectiveDivisor (F := PaperFmod D) :=
  (Finsupp.single (paperBadBasePlace D b) (1 : NNReal), fun _ => 0)

/-- The global q_v zero-locus divisor: the finite sum of the actual prime
divisors at all bad base places. -/
noncomputable def paperQVZeroLocusGlobal (D : S1895PaperInput) :
    RealEffectiveDivisor (F := PaperFmod D) :=
  letI := (S1895PaperInput.I D).initial.bad_finite
  Finset.univ.sum (fun b : (S1895PaperInput.I D).initial.badPlaces => paperQVZeroLocusPrime D b)

/-- The global zero-locus divisor is exactly the finite sum of the local prime
divisors. -/
theorem paperQVZeroLocusGlobal_eq_sum (D : S1895PaperInput) :
    paperQVZeroLocusGlobal D =
      (letI := (S1895PaperInput.I D).initial.bad_finite
       Finset.univ.sum (fun b : (S1895PaperInput.I D).initial.badPlaces =>
        paperQVZeroLocusPrime D b)) := rfl

/-- Each local q_v zero-locus divisor has the actual bad base prime in its
finite support. -/
theorem paperQVZeroLocusPrime_support (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    (paperQVZeroLocusPrime D b).1 (paperBadBasePlace D b) = 1 := by
  simp [paperQVZeroLocusPrime]

/-! ## 3. The finite global log-shell/tensor packet -/

/-- The actual local log-shell datum at a finite prime place of the S1895
one-column.  The log-coordinate field is Real; the units are the units of the
actual completed local field; the invariant submonoid is the full unit group
(the Galois action is not modeled, exactly as in the reduced carrier); the log
map is the actual norm-log degree. -/
noncomputable def paperLogShellDatum (v : FinitePrimePlace 2 7) :
    SourceLogShellDatum where
  p := v.1
  hp := v.2.2.2
  K := Real
  Units := (actualLocalField v)ˣ
  invariants := ⊤
  logMap := unitNormLogDegree (actualLocalField v)

/-- The actual finite global log-shell family over the one-column index V. -/
noncomputable def paperGlobalLogShellFamily :
    FinitePrimePlace 2 7 -> SourceLogShellDatum :=
  paperLogShellDatum

/-- The finite global log-shell direct-sum packet IQ(sum_v I_v). -/
noncomputable def paperGlobalLogShellPacket :
    Submodule Rat (FinitePrimePlace 2 7 -> Real) :=
  sourceLogShellIQDirectSumPacket paperGlobalLogShellFamily

/-- The packet is exactly the Q-span of the product of the actual local
log-shells. -/
theorem paperGlobalLogShellPacket_eq_span :
    paperGlobalLogShellPacket =
      Submodule.span Rat
        (sourceLogShellDirectSumPacketSet paperGlobalLogShellFamily) :=
  sourceLogShellIQDirectSumPacket_eq_span_pi paperGlobalLogShellFamily

/-- The reduced n-tensor log-shell packet over a finite factor set. -/
noncomputable def paperGlobalLogShellTensorPacket
    {A : Type} [Fintype A] (t : A -> Set Real) : Set Real :=
  sourceLogShellTensorProductSet t

/-- The tensor-packet Q-span decomposition. -/
theorem paperGlobalLogShellTensorPacket_span_eq
    {A : Type} [Fintype A] [DecidableEq A] (t : A -> Set Real) :
    Submodule.span Rat (paperGlobalLogShellTensorPacket t) =
      Submodule.span Rat
        (paperGlobalLogShellTensorPacket
          (fun a => (Submodule.span Rat (t a) : Set Real))) :=
  sourceLogShellTensorProductSet_span_eq t

/-! ## 4. The exact first missing: the archimedean log-shell -/

/-- The actual closed unit ball in the archimedean completion of Fmod at w. -/
def archimedeanUnitBall (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) : Set w.Completion :=
  {x | ‖x‖ ≤ 1}

/-- The archimedean log-shell datum at an actual infinite place w of Fmod: a
compact convex set of the actual completion w.Completion, contained in the
actual closed unit ball and containing 0.  This is the reduced shape of IUT
III, Definition 1.1, (ii).  It is a different carrier from SourceLogShellDatum,
which is nonarchimedean (it carries a prime p and a (p*_v)^{-1}-scaled
pre-log-shell). -/
structure ArchimedeanLogShellDatum (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) where
  [moduleK : Module Real w.Completion]
  /-- the archimedean log-shell (closed line segment / orbit) -/
  logShell : Set w.Completion
  /-- the log-shell is contained in the actual closed unit ball -/
  logShell_subset_unitBall : logShell ⊆ archimedeanUnitBall D w
  /-- the log-shell contains 0 -/
  zero_mem_logShell : (0 : w.Completion) ∈ logShell
  /-- the log-shell is convex over Real (the closed-interval shape) -/
  convex_logShell : Convex Real logShell
  /-- the log-shell is compact -/
  isCompact_logShell : IsCompact logShell

/-- The exact first missing object after the realified C-mod, the q_v
zero-locus divisor and the finite log-shell packet: an archimedean log-shell
datum at every archimedean place of Fmod.  No inhabitant is asserted. -/
def S1927FirstMissing (D : S1895PaperInput) : Type :=
  (w : NumberField.InfinitePlace (PaperFmod D)) -> ArchimedeanLogShellDatum D w

/-- A SourceLogShellDatum is nonarchimedean: it carries a prime p.  This is
the structural reason the existing reduced log-shell carrier cannot supply the
archimedean first missing above. -/
theorem sourceLogShellDatum_carries_prime (L : SourceLogShellDatum) :
    Exists (fun p : Nat => Nat.Prime p) := ⟨L.p, L.hp⟩

/-! ## 5. The full log-Kummer on 1,circ U_Q and its exact missing inputs -/

/-- The actual Kummer evaluation square of IUT III, Theorem 3.11, (iii), (a),
(b), on four source F-prime-strips.  The paper's four coric vertices
env/gau/LGP/lgp are not constructed in the tree (SourceKummerEvaluationArrows
R3); the type is therefore parameterized by its four strips and does not
pretend that they are the paper vertices.  No inhabitant is asserted. -/
structure S1927KummerEvaluationSquareActual (D : S1895PaperInput) where
  upperLeft : FPrimeStrip (FinitePrimePlace 2 7)
  upperRight : FPrimeStrip (FinitePrimePlace 2 7)
  lowerLeft : FPrimeStrip (FinitePrimePlace 2 7)
  lowerRight : FPrimeStrip (FinitePrimePlace 2 7)
  square : SourceKummerEvaluationSquare
    (S1895KummerGroup (S1895PaperInput.I D))
    upperLeft upperRight lowerLeft lowerRight

/-- The full log-Kummer package on 1,circ U_Q.  The one-column structure and
its (1,0) label are the actual S1895PaperO data; the finite log-shell packet is
the constructed one; the archimedean log-shell and the Kummer evaluation
square are the two named missing inputs. -/
structure S1927FullLogKummerUQ (D : S1895PaperInput) where
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure
    (FinitePrimePlace 2 7)
  oneColumn_eq : oneColumn = (S1895PaperO D).oneColumn
  label : S1895OneColumnLabel (FinitePrimePlace 2 7)
  label_eq : label = s1895PaperO_oneColumnLabel D
  finiteLogShell : Submodule Rat (FinitePrimePlace 2 7 -> Real)
  finiteLogShell_eq : finiteLogShell = paperGlobalLogShellPacket
  archimedeanLogShell : S1927FirstMissing D
  evaluationSquare : S1927KummerEvaluationSquareActual D

/-- Assembly of the full log-Kummer package from the constructed finite data
and the two named missing inputs. -/
noncomputable def s1927FullLogKummerUQ_of_missing
    (D : S1895PaperInput) (h : S1927FirstMissing D)
    (sq : S1927KummerEvaluationSquareActual D) :
    S1927FullLogKummerUQ D where
  oneColumn := (S1895PaperO D).oneColumn
  oneColumn_eq := rfl
  label := s1895PaperO_oneColumnLabel D
  label_eq := rfl
  finiteLogShell := paperGlobalLogShellPacket
  finiteLogShell_eq := rfl
  archimedeanLogShell := h
  evaluationSquare := sq

/-! ## 6. The constructed global package -/

/-- The three global objects constructed in this file, tied to the S1895 paper
input. -/
structure S1927ConstructedGlobalObjects (D : S1895PaperInput) where
  frobenioid : Iut.FrobenioidPresentation
  frobenioid_eq : frobenioid = paperGlobalRealifiedFrobenioid D
  qVZeroLocus : RealEffectiveDivisor (F := PaperFmod D)
  qVZeroLocus_eq : qVZeroLocus = paperQVZeroLocusGlobal D
  logShellPacket : Submodule Rat (FinitePrimePlace 2 7 -> Real)
  logShellPacket_eq : logShellPacket = paperGlobalLogShellPacket

/-- The global objects are constructed from the actual S1895 input, not from a
gate or an arbitrary inhabitant. -/
noncomputable def s1927ConstructedGlobalObjects (D : S1895PaperInput) :
    S1927ConstructedGlobalObjects D where
  frobenioid := paperGlobalRealifiedFrobenioid D
  frobenioid_eq := rfl
  qVZeroLocus := paperQVZeroLocusGlobal D
  qVZeroLocus_eq := rfl
  logShellPacket := paperGlobalLogShellPacket
  logShellPacket_eq := rfl

/-- Summary: the realified Frobenioid, the q_v zero-locus divisor and the
finite global log-shell packet are constructed; the full log-Kummer on
1,circ U_Q is assembled from the constructed finite data and the two named
missing inputs (archimedean log-shell and Kummer evaluation square). -/
theorem s1927_global_objects_and_firstMissing (D : S1895PaperInput) :
    And ((s1927ConstructedGlobalObjects D).frobenioid =
        paperGlobalRealifiedFrobenioid D)
      (And ((s1927ConstructedGlobalObjects D).qVZeroLocus =
          paperQVZeroLocusGlobal D)
        (And ((s1927ConstructedGlobalObjects D).logShellPacket =
            paperGlobalLogShellPacket)
          ((h : S1927FirstMissing D) ->
            (sq : S1927KummerEvaluationSquareActual D) ->
              Nonempty (S1927FullLogKummerUQ D)))) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h sq
  exact ⟨s1927FullLogKummerUQ_of_missing D h sq⟩

/-! ## 7. Axiom probes -/

#print axioms paperGlobalRealifiedFrobenioid
#print axioms paperGlobalRealifiedFrobenioid_divisorMonoid
#print axioms paperGlobalRealifiedFrobenioid_groupCompletion
#print axioms paperQVZeroLocusGlobal_eq_sum
#print axioms paperGlobalLogShellPacket_eq_span
#print axioms paperGlobalLogShellTensorPacket_span_eq
#print axioms s1927_global_objects_and_firstMissing

end LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual

end
