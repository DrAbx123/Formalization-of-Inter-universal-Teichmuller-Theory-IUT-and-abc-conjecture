import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# S2217: the Dedekind--Frobenius cycle-type theorem

The literal S2167 statement compares Mathlib's Equiv.Perm.cycleType (which omits
fixed points) with the multiset of degrees of all irreducible factors of f mod P
(which includes linear factors).  That statement is false: for f = X over
K = L = Q the right-hand side is {1} while every root is fixed, so the cycle type
is empty.  The mathematically correct statements are:

* orbit-size version: the multiset of orbit sizes of an arithmetic Frobenius on
  the roots of f (including fixed points) equals the multiset of irreducible
  factor degrees of f mod P;
* cycle-type version: Mathlib's cycle type is that multiset with the 1s removed.

This file proves the following unconditional infrastructure:

1. evaluation and derivative commute with reduction modulo P;
2. the root reduction map from O_L to O_L/P is injective, using separability of
   the reduction (Splits.eval_root_derivative plus Separable.eval2_derivative_ne_zero);
3. f splits over O_L and its roots are distinct, so the root set has cardinality
   natDegree f; consequently the root reduction map is bijective;
4. the finite-field orbit-size lemmas: for a monic irreducible g over the residue
   field, the q-Frobenius orbit of a root of g has size natDegree g;
5. a general combinatorial theorem cycleType_eq_fiber_sizes: if a permutation
   preserves the fibres of a map and acts transitively on each fibre, its cycle
   type is the multiset of fibre sizes >= 2.

The literal S2167 statement is moreover formally refuted here
(s2167_literal_statement_false): for f = X over Q its factor-degree multiset is
{1}, while Mathlib's cycle type never contains 1.

The remaining missing step is the instantiation of 5 with the minpoly fibres and
the identification of the resulting multiset with factorDegrees (f mod P); see
S2217Missing below.  No sorry, admit, axiom, opaque declaration or native_decide
is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Polynomial
open NumberField

attribute [local instance] Ideal.Quotient.field

namespace LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual

open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

/-- The polynomial f viewed over K. -/
noncomputable def q (f : (RingOfIntegers K)[X]) : K[X] :=
  f.map (algebraMap (RingOfIntegers K) K)

/-- The reduction of f modulo p. -/
noncomputable def fbar (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) :
    ((RingOfIntegers K) ⧸ p)[X] :=
  f.map (Ideal.Quotient.mk p)

section FiberCycleType

/-- Combinatorial lemma: if a permutation preserves the fibres of a map and acts
transitively on each fibre, then its cycle type is the multiset of sizes of the
fibres of size at least two. -/
theorem cycleType_eq_fiber_sizes
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) (p : α → β) (d : β → ℕ)
    (hinv : ∀ x, p (σ x) = p x)
    (hcard : ∀ b, Fintype.card {x // p x = b} = d b)
    (htrans : ∀ b (x y : α), p x = b → p y = b → σ.SameCycle x y) :
    σ.cycleType = (Finset.univ.filter (fun b => 2 ≤ d b)).val.map d := by
  classical
  let T : Finset β := Finset.univ.filter (fun b => 2 ≤ d b)
  let fib : β → Set α := fun b => {x | p x = b}
  have hfibInv : ∀ b x, fib b (σ x) ↔ fib b x := by
    intro b x
    change p (σ x) = b ↔ p x = b
    rw [hinv x]
  let cyc : β → Equiv.Perm α := fun b => (σ.subtypePerm (hfibInv b)).ofSubtype
  have hcyc_apply_mem : ∀ b (x : α), p x = b → cyc b x = σ x := by
    intro b x hx
    change (Equiv.Perm.ofSubtype (σ.subtypePerm (hfibInv b))) x = σ x
    rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fib b) (ha := hx)]
    rw [Equiv.Perm.subtypePerm_apply]
  have hcyc_apply_not_mem : ∀ b (x : α), p x ≠ b → cyc b x = x := by
    intro b x hx
    change (Equiv.Perm.ofSubtype (σ.subtypePerm (hfibInv b))) x = x
    exact Equiv.Perm.ofSubtype_apply_of_not_mem (p := fib b) (f := σ.subtypePerm (hfibInv b)) hx
  have hon : ∀ b, σ.IsCycleOn (fib b) := by
    intro b
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact fun x hx => (hfibInv b x).mpr hx
    · exact fun x hx y hy hxy => σ.injective hxy
    · intro y hy
      refine ⟨σ⁻¹ y, ?_, σ.apply_symm_apply y⟩
      apply (hfibInv b (σ⁻¹ y)).mp
      have h2 : σ (σ⁻¹ y) = y := σ.apply_symm_apply y
      rw [h2]
      exact hy
    · intro y hy z hz
      exact htrans b y z hy hz
  have hfib_nontriv : ∀ b, 2 ≤ d b → (fib b).Nontrivial := by
    intro b hb
    have hc : 1 < Fintype.card {x // p x = b} := by rw [hcard]; omega
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hc
    exact ⟨x.1, by simp [fib], y.1, by simp [fib], fun h => hxy (Subtype.ext h)⟩
  have hcyc_cycle : ∀ b, 2 ≤ d b → (cyc b).IsCycle := by
    intro b hb
    have hsub : (σ.subtypePerm (hfibInv b)).IsCycle :=
      (hon b).isCycle_subtypePerm (hfib_nontriv b hb)
    rw [← Equiv.Perm.card_cycleType_eq_one, Equiv.Perm.cycleType_ofSubtype, hsub.cycleType]
    simp
  have hcyc_support : ∀ b, 2 ≤ d b → (cyc b).support = (fib b).toFinset := by
    intro b hb
    ext x
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hx
      rw [Set.mem_toFinset]
      by_contra hxb
      exact hx (hcyc_apply_not_mem b x hxb)
    · intro hx
      rw [Set.mem_toFinset] at hx
      rw [hcyc_apply_mem b x hx]
      exact (hon b).apply_ne (hfib_nontriv b hb) hx
  have hcyc_support_card : ∀ b, 2 ≤ d b → (cyc b).support.card = d b := by
    intro b hb
    rw [hcyc_support b hb, Set.toFinset_card]
    change Fintype.card {x // p x = b} = d b
    exact hcard b
  have hdisjoint : (T : Set β).Pairwise
      (fun b b' => Equiv.Perm.Disjoint (cyc b) (cyc b')) := by
    intro b hb b' hb' hne
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    rw [hcyc_support b (Finset.mem_filter.mp hb).2] at hx
    rw [hcyc_support b' (Finset.mem_filter.mp hb').2] at hx'
    rw [Set.mem_toFinset] at hx hx'
    exact hne (hx.symm.trans hx')
  have hcomm : (T : Set β).Pairwise
      (fun b b' => Commute (cyc b) (cyc b')) :=
    hdisjoint.imp (fun _ _ h => h.commute)
  have hprod_aux : ∀ (s : Finset β)
      (hs : (s : Set β).Pairwise (fun b b' => Commute (cyc b) (cyc b'))),
      ∀ x : α, s.noncommProd cyc hs x = if p x ∈ s then σ x else x := by
    intro s hs x
    induction s using Finset.induction_on generalizing x with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
        simp only [Equiv.Perm.mul_apply]
        rw [ih]
        by_cases hpa : p x = a
        · have hnotmem : p x ∉ s := by rw [hpa]; exact ha
          rw [if_neg hnotmem, hcyc_apply_mem a x hpa]
          simp [hpa]
        · by_cases hxs : p x ∈ s
          · rw [if_pos hxs, hcyc_apply_not_mem a (σ x) (by rw [hinv x]; exact hpa)]
            rw [if_pos (by simp [hpa, hxs])]
          · rw [if_neg hxs, hcyc_apply_not_mem a x hpa]
            rw [if_neg (by simp [hpa, hxs])]
  have hprod : T.noncommProd cyc hcomm = σ := by
    ext x
    rw [hprod_aux T hcomm x]
    by_cases hxT : p x ∈ T
    · rw [if_pos hxT]
    · rw [if_neg hxT]
      have hlt : d (p x) < 2 := by
        by_contra h
        exact hxT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      have hsub : Subsingleton {y // p y = p x} := by
        rw [← Fintype.card_le_one_iff_subsingleton, hcard]
        omega
      have hmem : (⟨x, rfl⟩ : {y // p y = p x}) = ⟨σ x, hinv x⟩ := Subsingleton.elim _ _
      have hval : σ x = x := by
        have := congrArg Subtype.val hmem
        simpa using this.symm
      exact hval.symm
  calc σ.cycleType = (T.noncommProd cyc hcomm).cycleType := by rw [hprod]
    _ = T.sum (fun b => (cyc b).cycleType) :=
        Equiv.Perm.Disjoint.cycleType_noncommProd hdisjoint hcomm
    _ = T.sum (fun b => ({d b} : Multiset ℕ)) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [(hcyc_cycle b (Finset.mem_filter.mp hb).2).cycleType,
          hcyc_support_card b (Finset.mem_filter.mp hb).2]
    _ = T.val.map d := by
        induction T using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, ih, Finset.insert_val_of_notMem ha, Multiset.map_cons]
            simp

end FiberCycleType

section Main

variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)

include hp hP hPover in
/-- The prime P above a maximal ideal is maximal. -/
lemma P_ne_bot : P ≠ ⊥ := by
  intro hbot
  have hpbot : p = ⊥ := by
    rw [Ideal.over_def P p, hbot]
    exact Ideal.under_bot (RingOfIntegers K) (RingOfIntegers L)
  exact (Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)) hpbot

include hp hP hPover in
lemma P_isMaximal : P.IsMaximal :=
  Ideal.IsPrime.isMaximal hP (P_ne_bot p P)

include hp hP hPover in
/-- Evaluation commutes with reduction modulo P (general polynomial). -/
lemma mk_aeval_eq_of (g : (RingOfIntegers K)[X]) (α : RingOfIntegers L) :
    Ideal.Quotient.mk P (aeval α g) =
      (g.map (Ideal.Quotient.mk p)).eval₂
        (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))
        (Ideal.Quotient.mk P α) := by
  rw [aeval_def, eval₂_map]
  rw [show (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)).comp
        (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk P).comp (algebraMap (RingOfIntegers K) (RingOfIntegers L)) from by
    ext x
    exact Ideal.Quotient.algebraMap_mk_of_liesOver P p x]
  rw [← eval₂_map, eval₂_hom, eval_map]

include hp hP hPover in
/-- Derivative version of the evaluation compatibility. -/
lemma mk_aeval_derivative_eq (g : (RingOfIntegers K)[X]) (α : RingOfIntegers L) :
    Ideal.Quotient.mk P (aeval α (derivative g)) =
      (derivative (g.map (Ideal.Quotient.mk p))).eval₂
        (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))
        (Ideal.Quotient.mk P α) := by
  rw [derivative_map]
  exact mk_aeval_eq_of p P (derivative g) α

include hp hP hPover in
/-- The reduction of a root of f in the ring of integers is a root of f modulo P. -/
lemma mk_mem_rootSet (hmonic : f.Monic) (α : RingOfIntegers L)
    (hα : α ∈ f.rootSet (RingOfIntegers L)) :
    Ideal.Quotient.mk P α ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) := by
  rw [mem_rootSet']
  constructor
  · exact Polynomial.map_monic_ne_zero
      (Polynomial.Monic.map (Ideal.Quotient.mk p) hmonic)
  · rw [fbar, aeval_def, ← mk_aeval_eq_of p P f α]
    rw [mem_rootSet'] at hα
    rw [hα.2, map_zero]

include hp hP hPover in
/-- A root of f in the ring of integers has nonvanishing derivative modulo P. -/
lemma aeval_derivative_ne_zero (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (α : RingOfIntegers L) (hα : α ∈ f.rootSet (RingOfIntegers L)) :
    aeval α (derivative f) ≠ 0 := by
  haveI : P.IsMaximal := P_isMaximal p P
  intro hzero
  have hroot : (fbar f p).eval₂
      (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))
      (Ideal.Quotient.mk P α) = 0 := by
    rw [fbar, ← mk_aeval_eq_of p P f α]
    rw [mem_rootSet'] at hα
    rw [hα.2, map_zero]
  have hne := hsep.eval₂_derivative_ne_zero
    (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) hroot
  apply hne
  rw [fbar, derivative_map, ← mk_aeval_eq_of p P (derivative f) α, hzero, map_zero]

include hp hP hPover in
/-- f splits over the ring of integers of L. -/
lemma splits_over_ringOfIntegers (hmonic : f.Monic)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) :
    (f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).Splits := by
  have hmap : f.map (algebraMap (RingOfIntegers K) L) =
      (f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).map
        (algebraMap (RingOfIntegers L) L) := by
    rw [Polynomial.map_map,
      IsScalarTower.algebraMap_eq (RingOfIntegers K) (RingOfIntegers L) L]
  refine Polynomial.Splits.of_splits_map_of_injective
    (f := f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L)))
    (i := algebraMap (RingOfIntegers L) L) RingOfIntegers.coe_injective ?_ ?_
  · rw [← hmap]; exact hsplit
  · intro a ha
    rw [← hmap] at ha
    have hfne : f.map (algebraMap (RingOfIntegers K) L) ≠ 0 :=
      Polynomial.map_monic_ne_zero hmonic
    have hroot : aeval a f = 0 := by
      rw [mem_roots hfne] at ha
      simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using ha
    have hint : IsIntegral (RingOfIntegers K) a := ⟨f, hmonic, hroot⟩
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff
      (A := RingOfIntegers L) (R := RingOfIntegers K) (B := L)).mp hint
    exact ⟨y, hy⟩

include hp hP hPover in
/-- The roots of f over the ring of integers of L are distinct. -/
lemma roots_nodup (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) :
    (f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).roots.Nodup := by
  classical
  set fS := f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L)) with hfS
  have hfS_monic : fS.Monic := Polynomial.Monic.map _ hmonic
  have hfS_ne : fS ≠ 0 := hfS_monic.ne_zero
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [Polynomial.count_roots]
  by_contra h
  push Not at h
  have hlt : 1 < fS.rootMultiplicity a := h
  have hrootd := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hfS_ne).mp hlt
  have hmem : a ∈ f.rootSet (RingOfIntegers L) := by
    rw [mem_rootSet']
    constructor
    · exact Polynomial.map_monic_ne_zero hmonic
    · simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, hfS] using hrootd.1
  have hder := aeval_derivative_ne_zero f p P hmonic hsep a hmem
  apply hder
  simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, hfS,
    Polynomial.derivative_map] using hrootd.2

include hp hP hPover in
/-- The number of roots of f in the ring of integers of L is the degree of f. -/
lemma card_rootSet_eq (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) :
    Fintype.card (f.rootSet (RingOfIntegers L)) = f.natDegree := by
  classical
  have hsplitS := splits_over_ringOfIntegers f p P hmonic hsplit
  have hnodup := roots_nodup f p P hmonic hsep hsplit
  simp_rw [Polynomial.rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplitS.natDegree_eq_card_roots]
  exact Polynomial.Monic.natDegree_map hmonic
    (algebraMap (RingOfIntegers K) (RingOfIntegers L))

include hp hP hPover in
/-- The reduction map from roots of f in the ring of integers of L to roots of f mod P. -/
noncomputable def redRoot : f.rootSet (RingOfIntegers L) →
    (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) :=
  fun α => ⟨Ideal.Quotient.mk P α.1, mk_mem_rootSet f p P hmonic α.1 α.2⟩

include hp hP hPover in
/-- The reduction map on roots is injective. -/
lemma redRoot_injective (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) :
    Function.Injective (redRoot f p P hmonic) := by
  classical
  rintro ⟨α, hα⟩ ⟨β, hβ⟩ h
  have hmod : Ideal.Quotient.mk P α = Ideal.Quotient.mk P β := congrArg Subtype.val h
  by_contra hne
  have hne' : α ≠ β := fun h' => hne (Subtype.ext h')
  have hsplitS := splits_over_ringOfIntegers f p P hmonic hsplit
  have hfS_monic : (f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).Monic :=
    Polynomial.Monic.map _ hmonic
  have hfS_ne : f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L)) ≠ 0 :=
    hfS_monic.ne_zero
  have hαroot : α ∈ (f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).roots := by
    rw [mem_roots hfS_ne]
    rw [mem_rootSet'] at hα
    simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hα.2
  have hβroot : β ∈ (f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).roots := by
    rw [mem_roots hfS_ne]
    rw [mem_rootSet'] at hβ
    simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hβ.2
  have hβerase : β ∈ ((f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).roots.erase α) :=
    (Multiset.mem_erase_of_ne (Ne.symm hne')).mpr hβroot
  have hmemP : α - β ∈ P := Ideal.Quotient.eq.mp hmod
  have hprodmem : ((((f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).roots.erase α).map
      (fun γ => α - γ))).prod ∈ P :=
    Ideal.mem_of_dvd P (Multiset.dvd_prod (Multiset.mem_map.mpr ⟨β, hβerase, rfl⟩)) hmemP
  have hderiv := hsplitS.eval_root_derivative hfS_monic hαroot
  have hderivmem : aeval α (derivative f) ∈ P := by
    rw [aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map]
    rw [hderiv]
    exact hprodmem
  have hrootbar : (fbar f p).eval₂
      (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))
      (Ideal.Quotient.mk P α) = 0 := by
    rw [fbar, ← mk_aeval_eq_of p P f α]
    rw [mem_rootSet'] at hα
    rw [hα.2, map_zero]
  have hneDeriv := hsep.eval₂_derivative_ne_zero
    (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) hrootbar
  apply hneDeriv
  rw [fbar, ← mk_aeval_derivative_eq p P f α]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hderivmem

include hp hP hPover in
/-- Cardinality bound for the roots of f modulo P. -/
lemma card_rootSet_fbar_le (hmonic : f.Monic) :
    Fintype.card ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) ≤ f.natDegree := by
  classical
  have h1 : Fintype.card ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) =
      (((fbar f p).aroots ((RingOfIntegers L) ⧸ P)).toFinset).card :=
    Fintype.card_coe _
  rw [h1]
  calc (((fbar f p).aroots ((RingOfIntegers L) ⧸ P)).toFinset).card
      ≤ ((fbar f p).aroots ((RingOfIntegers L) ⧸ P)).card := Multiset.toFinset_card_le _
    _ = ((fbar f p).map (algebraMap ((RingOfIntegers K) ⧸ p)
          ((RingOfIntegers L) ⧸ P))).roots.card := rfl
    _ ≤ (fbar f p).natDegree := Polynomial.card_roots_map_le_natDegree _
    _ = f.natDegree := Polynomial.Monic.natDegree_map hmonic (Ideal.Quotient.mk p)

include hp hP hPover in
/-- The reduction map on roots is a bijection. -/
lemma redRoot_bijective (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) :
    Function.Bijective (redRoot f p P hmonic) := by
  classical
  have hdom : Fintype.card (f.rootSet (RingOfIntegers L)) = f.natDegree :=
    card_rootSet_eq f p P hmonic hsep hsplit
  have hle := card_rootSet_fbar_le f p P hmonic
  have hinj := redRoot_injective f p P hmonic hsep hsplit
  have hcard_le : Fintype.card (f.rootSet (RingOfIntegers L)) ≤
      Fintype.card ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :=
    Fintype.card_le_of_injective _ hinj
  have hcard : Fintype.card (f.rootSet (RingOfIntegers L)) =
      Fintype.card ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) := by
    rw [hdom]
    exact le_antisymm (by rw [hdom] at hcard_le; exact hcard_le) hle
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

include hp hP hPover in
/-- The reduction equivalence between roots of f in the ring of integers and roots of f mod P. -/
noncomputable def redRootEquiv (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) :
    f.rootSet (RingOfIntegers L) ≃ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) :=
  Equiv.ofBijective _ (redRoot_bijective f p P hmonic hsep hsplit)

end Main

section FiniteFieldPart

variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)

include hp hP hPover in
/-- The arithmetic q-Frobenius on the residue field at P, where q is the
cardinality of the residue field at p. -/
noncomputable def frobBar (y : (RingOfIntegers L) ⧸ P) : (RingOfIntegers L) ⧸ P :=
  y ^ Nat.card ((RingOfIntegers K) ⧸ p)

include hp hP hPover in
lemma frobBar_mem_rootSet {y : (RingOfIntegers L) ⧸ P}
    (hy : y ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    frobBar p P y ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) := by
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Fintype ((RingOfIntegers K) ⧸ p) := Fintype.ofFinite _
  haveI : Fintype ((RingOfIntegers L) ⧸ P) := Fintype.ofFinite _
  rw [mem_rootSet'] at hy ⊢
  refine ⟨hy.1, ?_⟩
  have h := Polynomial.aeval_algHom_apply
    (FiniteField.frobeniusAlgHom ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))
    y (fbar f p)
  rw [hy.2, map_zero] at h
  have hfrob : FiniteField.frobeniusAlgHom ((RingOfIntegers K) ⧸ p)
      ((RingOfIntegers L) ⧸ P) y = y ^ Nat.card ((RingOfIntegers K) ⧸ p) := by
    rw [FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [frobBar, ← hfrob]
  exact h

include hp hP hPover in
/-- The q-Frobenius is injective on the residue field. -/
lemma frobBar_injective : Function.Injective (frobBar p P) := by
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Fintype ((RingOfIntegers K) ⧸ p) := Fintype.ofFinite _
  haveI : Fintype ((RingOfIntegers L) ⧸ P) := Fintype.ofFinite _
  have h := RingHom.injective
    (FiniteField.frobeniusAlgHom ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)).toRingHom
  intro y z hyz
  apply h
  simpa [frobBar, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card] using hyz

include hp hP hPover in
/-- The q-Frobenius as a permutation of the roots of f modulo P. -/
noncomputable def permBar : Equiv.Perm ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :=
  Equiv.ofBijective
    (fun y => ⟨frobBar p P y.1, frobBar_mem_rootSet f p P y.2⟩)
    (Finite.injective_iff_bijective.mp (fun y z h => Subtype.ext
      (frobBar_injective p P (congrArg Subtype.val h))))


include hp hP hPover in
/-- The iterates of the q-Frobenius are power maps. -/
lemma frobBar_iterate (n : ℕ) (y : (RingOfIntegers L) ⧸ P) :
    (frobBar p P)^[n] y = y ^ (Nat.card ((RingOfIntegers K) ⧸ p)) ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, frobBar, ← pow_mul, ← pow_succ]

include hp hP hPover in
/-- Frobenius sends roots of a polynomial over the base residue field to roots. -/
lemma aeval_frobBar (g : ((RingOfIntegers K) ⧸ p)[X]) (x : (RingOfIntegers L) ⧸ P) :
    aeval (frobBar p P x) g = (aeval x g) ^ Nat.card ((RingOfIntegers K) ⧸ p) := by
  haveI : Fintype ((RingOfIntegers K) ⧸ p) := Fintype.ofFinite _
  have h := Polynomial.aeval_algHom_apply
    (FiniteField.frobeniusAlgHom ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) x g
  simpa [frobBar, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card] using h

include hp hP hPover in
/-- The order of the q-Frobenius orbit of a root of a monic irreducible g is
bounded below by the degree of g. -/
lemma frobBar_iterate_ne_self {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic)
    (hirr : Irreducible g) {x : (RingOfIntegers L) ⧸ P} (hx : aeval x g = 0)
    {n : ℕ} (hn0 : 0 < n) (hnd : n < g.natDegree) :
    (frobBar p P)^[n] x ≠ x := by
  haveI : P.IsMaximal := P_isMaximal p P
  intro h
  have hmin : minpoly ((RingOfIntegers K) ⧸ p) x = g := by
    have h := minpoly.eq_of_irreducible hirr hx
    simpa [hg.leadingCoeff] using h.symm
  have hpow : x ^ (Nat.card ((RingOfIntegers K) ⧸ p)) ^ n = x := by
    rw [← frobBar_iterate p P n x]
    exact h
  have hdvd : g ∣ Polynomial.X ^ (Nat.card ((RingOfIntegers K) ⧸ p)) ^ n - Polynomial.X := by
    rw [← hmin]
    refine minpoly.dvd ((RingOfIntegers K) ⧸ p) x ?_
    rw [map_sub, map_pow, aeval_X, hpow, sub_self]
  have hdvd' : g.natDegree ∣ n :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hirr hdvd
  exact absurd hnd (not_lt.mpr (Nat.le_of_dvd hn0 hdvd'))

include hp hP hPover in
/-- The q-Frobenius fixes a root of a monic irreducible g after g.natDegree steps. -/
lemma frobBar_iterate_natDegree {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic)
    (hirr : Irreducible g) {x : (RingOfIntegers L) ⧸ P} (hx : aeval x g = 0) :
    (frobBar p P)^[g.natDegree] x = x := by
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Fintype ((RingOfIntegers K) ⧸ p) := Fintype.ofFinite _
  haveI : Fintype ((RingOfIntegers L) ⧸ P) := Fintype.ofFinite _
  have hmin : minpoly ((RingOfIntegers K) ⧸ p) x = g := by
    have h := minpoly.eq_of_irreducible hirr hx
    simpa [hg.leadingCoeff] using h.symm
  have hint : IsIntegral ((RingOfIntegers K) ⧸ p) x := ⟨g, hg, hx⟩
  let Kx : IntermediateField ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P) :=
    IntermediateField.adjoin ((RingOfIntegers K) ⧸ p) {x}
  have hxK : x ∈ Kx := IntermediateField.mem_adjoin_simple_self ((RingOfIntegers K) ⧸ p) x
  haveI : FiniteDimensional ((RingOfIntegers K) ⧸ p) Kx :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Fintype Kx := Fintype.ofFinite _
  have hfin : Module.finrank ((RingOfIntegers K) ⧸ p) Kx = g.natDegree := by
    rw [IntermediateField.adjoin.finrank hint, hmin]
  have hcard : Nat.card Kx = Nat.card ((RingOfIntegers K) ⧸ p) ^ g.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := (RingOfIntegers K) ⧸ p) (V := Kx), hfin]
  have hpow : (⟨x, hxK⟩ : Kx) ^ Nat.card Kx = ⟨x, hxK⟩ := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hpowF : x ^ Nat.card ((RingOfIntegers K) ⧸ p) ^ g.natDegree = x := by
    have := congrArg Subtype.val hpow
    rwa [hcard] at this
  rw [frobBar_iterate, hpowF]

end FiniteFieldPart

section CorrectedStatements

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

/-- The multiset of orbit sizes of a permutation, including fixed points
(one entry per orbit).  This is the "cycle type with 1s" of the classical
Dedekind--Frobenius theorem. -/
noncomputable def orbitSizeMultiset {α : Type*} [Fintype α] (σ : Equiv.Perm α) : Multiset ℕ :=
  letI := Classical.decEq α
  σ.cycleType + Multiset.replicate (Fintype.card (Function.fixedPoints σ)) 1

variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)

/-- The corrected orbit-size Dedekind--Frobenius statement: some arithmetic
Frobenius at P has orbit-size multiset equal to the multiset of degrees of the
irreducible factors of f modulo P (including linear factors). -/
def DedekindFrobeniusOrbitSizeStatement (hmonic : f.Monic)
    (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) : Prop :=
  ∃ sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P ∧
    orbitSizeMultiset (rootPerm K L f hsplit sigma) = factorDegrees (fbar f p)

/-- The corrected Dedekind--Frobenius cycle-type statement: Mathlib's cycle type
(which omits fixed points) equals the factor-degree multiset with the 1s removed. -/
def DedekindFrobeniusCycleTypeStatementCorrected (hmonic : f.Monic)
    (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) : Prop :=
  ∃ sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P ∧
    rootCycleType K L f hsplit sigma = (factorDegrees (fbar f p)).filter (fun n => n ≠ 1)

/-- The corrected orbit-size theorem, universally quantified. -/
def DedekindFrobeniusOrbitSizeTheorem : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits),
    DedekindFrobeniusOrbitSizeStatement f p P hmonic hsep hsplit

/-- The corrected cycle-type theorem, universally quantified. -/
def DedekindFrobeniusCycleTypeTheoremCorrected : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits),
    DedekindFrobeniusCycleTypeStatementCorrected f p P hmonic hsep hsplit

/-- The exact remaining missing theorem of S2217.  Its proof requires instantiating
cycleType_eq_fiber_sizes with the minpoly fibres (see the file header), which is
not formalized here. -/
def S2217Missing : Prop := DedekindFrobeniusOrbitSizeTheorem

/-- The literal S2167 identity has a linear factor counterexample: for f = X the
factor-degree multiset is {1}, while Mathlib's cycle type contains no 1
(Equiv.Perm.one_lt_of_mem_cycleType).  Hence the literal S2167 statement is false;
this lemma records the factor-degree half of the counterexample. -/
theorem factorDegrees_X (k : Type) [Field k] :
    factorDegrees (X : k[X]) = ({1} : Multiset ℕ) := by
  classical
  unfold factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X)]
  rw [Monic.normalize_eq_self (monic_X)]
  simp

/-- The literal S2167 statement DedekindFrobeniusCycleTypeTheorem is false.
Counterexample: K = L = Q, f = X, and P = p any maximal ideal of Z.
Then the reduced polynomial is X, whose factor-degree multiset is {1}, while
the root set of X is a singleton and hence the cycle type is empty; Mathlib's
cycle type never contains 1 (Equiv.Perm.one_lt_of_mem_cycleType). -/
theorem s2167_literal_statement_false : ¬ DedekindFrobeniusCycleTypeTheorem := by
  classical
  intro h
  obtain ⟨p, hp⟩ := Ideal.exists_maximal (RingOfIntegers ℚ)
  letI : p.IsMaximal := hp
  have hLies : p.LiesOver p := by
    refine ⟨?_⟩
    show p = Ideal.comap (algebraMap (RingOfIntegers ℚ) (RingOfIntegers ℚ)) p
    simp
  have hsplit : ((X : (RingOfIntegers ℚ)[X]).map
      (algebraMap (RingOfIntegers ℚ) ℚ)).Splits := by simp
  have hmain := h (K := ℚ) (L := ℚ) (f := (X : (RingOfIntegers ℚ)[X])) (p := p)
    (P := p) (hPover := hLies)
    (monic_X) (by simpa using (separable_X (R := (RingOfIntegers ℚ) ⧸ p))) hsplit
  obtain ⟨σ, -, hcyc⟩ := hmain
  have hfac : factorDegrees ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) =
      ({1} : Multiset ℕ) := by
    rw [show ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) =
        (X : ((RingOfIntegers ℚ) ⧸ p)[X]) by simp]
    exact factorDegrees_X _
  have hmem : (1 : ℕ) ∈ rootCycleType ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ := by
    rw [hcyc, hfac]
    simp
  letI : DecidableEq
      (((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).rootSet ℚ) :=
    Classical.decEq _
  have hlt : 1 < 1 :=
    Equiv.Perm.one_lt_of_mem_cycleType
      (σ := rootPerm ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ) hmem
  exact lt_irrefl 1 hlt

end CorrectedStatements

/-! ## Axiom footprint of the proved results -/

#print axioms cycleType_eq_fiber_sizes
#print axioms mk_aeval_eq_of
#print axioms mk_aeval_derivative_eq
#print axioms mk_mem_rootSet
#print axioms aeval_derivative_ne_zero
#print axioms splits_over_ringOfIntegers
#print axioms roots_nodup
#print axioms card_rootSet_eq
#print axioms redRoot_injective
#print axioms card_rootSet_fbar_le
#print axioms redRoot_bijective
#print axioms redRootEquiv
#print axioms frobBar_mem_rootSet
#print axioms frobBar_injective
#print axioms permBar
#print axioms frobBar_iterate
#print axioms aeval_frobBar
#print axioms frobBar_iterate_ne_self
#print axioms frobBar_iterate_natDegree
#print axioms factorDegrees_X
#print axioms s2167_literal_statement_false

end LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
