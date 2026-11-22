/-
S2445: final clean D5 corrected Dedekind--Frobenius application.

This file proves, unconditionally, the corrected Dedekind--Frobenius statements
for the arithmetic Frobenius at a prime of a Galois extension of number fields:

* the corrected cycle-type statement (S2217):
  the cycle type of the Frobenius on the roots is the multiset of irreducible
  factor degrees of the reduction, with the linear factors removed;
* the orbit-size statement S2217Missing: the multiset of orbit sizes including
  fixed points equals the full multiset of irreducible factor degrees.

The proof instantiates the abstract combinatorial theorem
cycleType_eq_fiber_sizes (S2217) with the root-to-factor map
s2425RootFactor (S2425), uses the fibre-size count s2408FiberSet_ncard
(S2408), the filter bridge s2428_filter_fiberSizes_eq_factorDegrees_filter
(S2428), and transports the cycle type from the residue-root permutation
permBar to the genuine root permutation via
s2440_permBar_cycleType_eq_rootCycleType (S2440).  Fibre transitivity is the
unconditional q-Frobenius transitivity s2339FrobTransitive.

No sorry, admit, axiom, opaque declaration, True, PUnit or native_decide is
used.  The axiom footprint is printed at the end.
-/
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2425PermBarInvarianceActual
import tmp.sheaf.xif.paper.S2408FiberSizesActual
import tmp.sheaf.xif.paper.S2428FilterBridgeActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
import Mathlib.FieldTheory.Perfect

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
open LeanFormal.IUT.XiFPaper.S2428FilterBridgeActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
open LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
open LeanFormal.IUT.XiFPaper.S2381SmulCommActual

namespace LeanFormal.IUT.XiFPaper.S2445D5FinalActual

attribute [local instance] Ideal.Quotient.field

/-! ## 0. General combinatorial lemmas -/

/-- Reindexing lemma: for a nodup multiset M, the multiset of the values of d
on the finite subtype of elements of M, filtered by 2 ≤ d, is the same as the
filtered map of d on M itself. -/
lemma s2445_univ_subtype_filter_map {α : Type*} [DecidableEq α] (M : Multiset α)
    (hM : M.Nodup) (d : α → ℕ) :
    (Finset.univ.filter (fun b : {x // x ∈ M} => 2 ≤ d b.1)).val.map (fun b => d b.1) =
      (M.map d).filter (fun n => 2 ≤ n) := by
  classical
  have huniv : (Finset.univ : Finset {x // x ∈ M}).val = M.attach := by
    show (M.attach.toFinset).val = M.attach
    rw [Multiset.toFinset_val, hM.attach.dedup]
  rw [Finset.filter_val, huniv]
  calc (M.attach.filter (fun a : {x // x ∈ M} => 2 ≤ d a.1)).map (fun a => d a.1)
      = (((M.filter (fun a => 2 ≤ d a)).attach).map
          (Subtype.map id (fun a ha => Multiset.mem_of_mem_filter ha))).map
            (fun a => d a.1) := by
        rw [Multiset.filter_attach]
    _ = ((M.filter (fun a => 2 ≤ d a)).attach).map
          (fun a => d (Subtype.map id (fun a ha => Multiset.mem_of_mem_filter ha) a).1) := by
        rw [Multiset.map_map]
        rfl
    _ = ((M.filter (fun a => 2 ≤ d a)).attach).map (fun a => d a.1) := by
        apply Multiset.map_congr rfl
        intro a _
        rfl
    _ = (M.filter (fun a => 2 ≤ d a)).map d := Multiset.attach_map_val' _ _
    _ = (M.map d).filter (fun n => 2 ≤ n) := by
        rw [Multiset.filter_map]

/-- A multiset of natural numbers is the multiset of its entries different from
one together with a suitable number of ones. -/
lemma s2445_filter_ne_one_add_replicate_count_one (M : Multiset ℕ) :
    M.filter (fun n => n ≠ 1) + Multiset.replicate (M.count 1) 1 = M := by
  classical
  ext n
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hn : n = 1
  · subst hn
    simp
  · have h1n : ¬ (1 = n) := fun h => hn h.symm
    simp [hn, h1n]

/-! ## 1. The main construction -/

section Main

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)

local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
local instance : DecidableEq ((RingOfIntegers L) ⧸ P) := Classical.decEq _
local instance : DecidableEq ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) := Classical.decEq _
local instance : DecidableEq (f.rootSet (RingOfIntegers L)) := Classical.decEq _
local instance : DecidableEq ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) := Classical.decEq _

/-- The root-to-factor map s2425RootFactor is invariant under permBar. -/
lemma s2445_rootFactor_permBar (x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    s2425RootFactor f p P hmonic hsep (permBar (f := f) p P x) =
      s2425RootFactor f p P hmonic hsep x :=
  s2425RootFactor_permBar f p P hmonic hsep x

/-- Iterates of permBar act on the underlying residue field as iterates of
frobBar. -/
lemma s2445_permBar_iterate_val (n : ℕ)
    (x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    ((permBar (f := f) p P)^[n] x).1 = (frobBar p P)^[n] x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

/-- The fibre of the root-to-factor map over a normalized irreducible factor is
equivalent to the set of residue roots whose minimal polynomial is that factor. -/
lemma s2445_fiber_equiv
    (b : {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
        s2425RootFactor f p P hmonic hsep x = b} ≃
      {y : (RingOfIntegers L) ⧸ P //
        y ∈ s2408FiberSet (K := K) (L := L) (p := p) (P := P) b.1} := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  obtain ⟨hg_irr, hg_monic, hg_dvd⟩ :=
    (Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)).mp b.2
  refine
    { toFun := fun x => ⟨x.1.1, ?_⟩
      invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun y => by apply Subtype.ext; rfl }
  · exact congrArg Subtype.val x.2
  · have hy : minpoly ((RingOfIntegers K) ⧸ p) y.1 = b.1 := y.2
    have hrootg : (Polynomial.aeval y.1) b.1 = 0 := by
      rw [← hy]
      exact minpoly.aeval _ _
    have hrootf : (Polynomial.aeval y.1) (fbar f p) = 0 :=
      Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hg_dvd hrootg
    exact (s2397Fbar_monic f p P hmonic).mem_rootSet.mpr hrootf
  · have hy : minpoly ((RingOfIntegers K) ⧸ p) y.1 = b.1 := y.2
    exact Subtype.ext hy

include hp hP hPover hmonic hsep hsplit in
/-- The fibre of the root-to-factor map over a normalized factor b has
cardinality equal to the number of roots of the fibre set, i.e. ncard. -/
lemma s2445_fiber_card
    (b : {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    Fintype.card {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
        s2425RootFactor f p P hmonic hsep x = b} =
      (s2408FiberSet (K := K) (L := L) (p := p) (P := P) b.1).ncard := by
  classical
  rw [Fintype.card_congr (s2445_fiber_equiv f p P hmonic hsep hsplit b)]
  exact (Nat.card_eq_fintype_card (α := ↥(s2408FiberSet (K := K) (L := L)
    (p := p) (P := P) b.1))).symm.trans (Nat.card_coe_set_eq _)

include hp hP hPover hmonic hsep hsplit in
/-- The arithmetic Frobenius acts transitively on each fibre of the
root-to-factor map. -/
lemma s2445_transitive
    (b : {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)})
    (x y : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P))
    (hx : s2425RootFactor f p P hmonic hsep x = b)
    (hy : s2425RootFactor f p P hmonic hsep y = b) :
    (permBar (f := f) p P).SameCycle x y := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  obtain ⟨hg_irr, hg_monic, hg_dvd⟩ :=
    (Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)).mp b.2
  have hminx : minpoly ((RingOfIntegers K) ⧸ p) x.1 = b.1 := congrArg Subtype.val hx
  have hminy : minpoly ((RingOfIntegers K) ⧸ p) y.1 = b.1 := congrArg Subtype.val hy
  have hax : (Polynomial.aeval x.1) b.1 = 0 := by
    rw [← hminx]
    exact minpoly.aeval _ _
  have hay : (Polynomial.aeval y.1) b.1 = 0 := by
    rw [← hminy]
    exact minpoly.aeval _ _
  obtain ⟨n, hn⟩ :=
    s2339FrobTransitive f p P hmonic hsep hsplit hg_monic hg_irr hg_dvd hax hay
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  change (permBar (f := f) p P ^ n) x = y
  rw [Equiv.Perm.coe_pow]
  apply Subtype.ext
  rw [s2445_permBar_iterate_val]
  exact hn

/-! ## 2. Cycle type of the residue-root permutation -/

include hp hP hPover hmonic hsep hsplit in
/-- The cycle type of the arithmetic q-Frobenius permutation of the residue
roots is the multiset of irreducible factor degrees with the linear factors
removed. -/
theorem s2445_permBar_cycleType_eq_factorDegrees_filter :
    (permBar (f := f) p P).cycleType =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have hcyc := cycleType_eq_fiber_sizes
    (σ := permBar (f := f) p P)
    (p := (s2425RootFactor f p P hmonic hsep :
      (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) →
        {g : ((RingOfIntegers K) ⧸ p)[X] //
          g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}))
    (d := fun b : {g : ((RingOfIntegers K) ⧸ p)[X] //
        g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} =>
      (s2408FiberSet (K := K) (L := L) (p := p) (P := P) b.1).ncard)
    (fun x => s2445_rootFactor_permBar f p P hmonic hsep hsplit x)
    (fun b => s2445_fiber_card f p P hmonic hsep hsplit b)
    (fun b x y hx hy => s2445_transitive f p P hmonic hsep hsplit b x y hx hy)
  rw [hcyc]
  have hM : (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).Nodup := by
    have hsq : Squarefree (fbar f p) := (PerfectField.separable_iff_squarefree).mp hsep
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (s2397Fbar_ne_zero f p P hmonic)).mp hsq
  rw [s2445_univ_subtype_filter_map
    (M := UniqueFactorizationMonoid.normalizedFactors (fbar f p)) hM
    (fun g => (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard)]
  exact s2428_filter_fiberSizes_eq_factorDegrees_filter
    (K := K) (L := L) f p P hmonic hsep hsplit

/-! ## 3. Bridge between the two standard actions on the ring of integers -/

/-- The Mathlib global MulSemiringAction of Gal(L/K) on O_L and the
integral-closure action used in S2440 have the same algebra homomorphisms; hence
the arithmetic-Frobenius predicates agree. -/
lemma s2445_isArithFrobAt_local
    (σ : Gal(L/K)) (P : Ideal (RingOfIntegers L))
    (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
     letI : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
        LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass
     IsArithFrobAt (RingOfIntegers K) σ P) := by
  classical
  let φg : RingOfIntegers L →ₐ[RingOfIntegers K] RingOfIntegers L :=
    MulSemiringAction.toAlgHom (RingOfIntegers K) (RingOfIntegers L) σ
  have hg : φg.IsArithFrobAt P := H
  letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
  letI : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
    LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass
  let φl : RingOfIntegers L →ₐ[RingOfIntegers K] RingOfIntegers L :=
    MulSemiringAction.toAlgHom (RingOfIntegers K) (RingOfIntegers L) σ
  have hφ : φg = φl := by
    ext x
    apply RingOfIntegers.coe_injective
    change algebraMap (RingOfIntegers L) L (φg x) = algebraMap (RingOfIntegers L) L (φl x)
    have hgl : algebraMap (RingOfIntegers L) L (φg x) =
        σ (algebraMap (RingOfIntegers L) L x) := rfl
    have hll : algebraMap (RingOfIntegers L) L (φl x) =
        σ (algebraMap (RingOfIntegers L) L x) :=
      algebraMap_galRestrict_apply (RingOfIntegers K) σ x
    rw [hgl, hll]
  change φl.IsArithFrobAt P
  rw [← hφ]
  exact hg

include hp hP hPover hmonic hsep hsplit in
/-- Corrected cycle-type statement for any arithmetic Frobenius at P. -/
theorem s2445_rootCycleType_eq_factorDegrees_filter
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    rootCycleType K L f hsplit σ =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
  letI : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
    LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass
  have Hloc : IsArithFrobAt (RingOfIntegers K) σ P :=
    s2445_isArithFrobAt_local f p P σ P H
  rw [← s2440_permBar_cycleType_eq_rootCycleType
    (K := K) (L := L) f p P hmonic hsep hsplit σ Hloc]
  exact s2445_permBar_cycleType_eq_factorDegrees_filter f p P hmonic hsep hsplit

/-! ## 4. The orbit-size multiset -/

include hp hP hPover hmonic hsep hsplit in
/-- The sum of the irreducible factor degrees is the degree of f. -/
lemma s2445_factorDegrees_sum :
    (factorDegrees (fbar f p)).sum = f.natDegree := by
  classical
  have hmonicbar : (fbar f p).Monic := s2397Fbar_monic f p P hmonic
  have hprod : (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).prod = fbar f p := by
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors (fbar f p)
    rw [hmonicbar.leadingCoeff, map_one, one_mul] at h
    exact h
  unfold factorDegrees
  rw [← Polynomial.natDegree_multiset_prod_of_monic]
  · rw [hprod]
    exact Polynomial.Monic.natDegree_map hmonic (Ideal.Quotient.mk p)
  · intro g hg
    exact ((Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)).mp hg).2.1

include hp hP hPover hmonic hsep hsplit in
/-- The orbit-size multiset (cycle type with fixed points) of an arithmetic
Frobenius at P equals the full multiset of irreducible factor degrees. -/
theorem s2445_orbitSizeMultiset_rootPerm_eq_factorDegrees
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    orbitSizeMultiset (rootPerm K L f hsplit σ) = factorDegrees (fbar f p) := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have hcyc : (rootPerm K L f hsplit σ).cycleType =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
    show rootCycleType K L f hsplit σ = _
    exact s2445_rootCycleType_eq_factorDegrees_filter f p P hmonic hsep hsplit σ H
  have hcardK : Fintype.card ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) =
      f.natDegree := by
    rw [← Fintype.card_congr (s2440RootSetEquiv (K := K) (L := L) f hmonic)]
    exact card_rootSet_eq f p P hmonic hsep hsplit
  have hsum := s2445_factorDegrees_sum f p P hmonic hsep hsplit
  have hcount : (factorDegrees (fbar f p)).count 1 =
      f.natDegree - ((factorDegrees (fbar f p)).filter (fun n => n ≠ 1)).sum := by
    have hid := s2445_filter_ne_one_add_replicate_count_one (factorDegrees (fbar f p))
    have hsumid : ((factorDegrees (fbar f p)).filter (fun n => n ≠ 1)).sum +
        (factorDegrees (fbar f p)).count 1 = f.natDegree := by
      have h := congrArg Multiset.sum hid
      rw [Multiset.sum_add, Multiset.sum_replicate, hsum] at h
      simpa using h
    omega
  unfold orbitSizeMultiset
  rw [Equiv.Perm.card_fixedPoints]
  rw [hcyc, hcardK, ← hcount]
  exact s2445_filter_ne_one_add_replicate_count_one (factorDegrees (fbar f p))

/-! ## 5. The universally quantified corrected theorems -/

/-- The corrected orbit-size Dedekind--Frobenius theorem, i.e. S2217Missing. -/
theorem s2445_dedekindFrobeniusOrbitSizeTheorem : DedekindFrobeniusOrbitSizeTheorem := by
  intro K L _ _ _ _ _ _ _ f p _ P _ _ _ hmonic hsep hsplit
  haveI : P.IsMaximal := P_isMaximal p P
  obtain ⟨σ, H⟩ := S2167FrobeniusExists K L P
  exact ⟨σ, H, s2445_orbitSizeMultiset_rootPerm_eq_factorDegrees
    f p P hmonic hsep hsplit σ H⟩

/-- The exact missing theorem of S2217. -/
theorem s2445_S2217Missing : S2217Missing :=
  s2445_dedekindFrobeniusOrbitSizeTheorem

/-- The corrected cycle-type Dedekind--Frobenius theorem. -/
theorem s2445_dedekindFrobeniusCycleTypeTheoremCorrected :
    DedekindFrobeniusCycleTypeTheoremCorrected := by
  intro K L _ _ _ _ _ _ _ f p _ P _ _ _ hmonic hsep hsplit
  haveI : P.IsMaximal := P_isMaximal p P
  obtain ⟨σ, H⟩ := S2167FrobeniusExists K L P
  exact ⟨σ, H, s2445_rootCycleType_eq_factorDegrees_filter
    f p P hmonic hsep hsplit σ H⟩

end Main

/-! ## 6. Axiom footprint -/

#print axioms s2445_univ_subtype_filter_map
#print axioms s2445_filter_ne_one_add_replicate_count_one
#print axioms s2445_fiber_equiv
#print axioms s2445_fiber_card
#print axioms s2445_transitive
#print axioms s2445_permBar_cycleType_eq_factorDegrees_filter
#print axioms s2445_isArithFrobAt_local
#print axioms s2445_rootCycleType_eq_factorDegrees_filter
#print axioms s2445_factorDegrees_sum
#print axioms s2445_orbitSizeMultiset_rootPerm_eq_factorDegrees
#print axioms s2445_dedekindFrobeniusOrbitSizeTheorem
#print axioms s2445_S2217Missing
#print axioms s2445_dedekindFrobeniusCycleTypeTheoremCorrected

end LeanFormal.IUT.XiFPaper.S2445D5FinalActual
end
