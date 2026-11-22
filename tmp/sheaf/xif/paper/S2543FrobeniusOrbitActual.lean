/-
S2543: Frobenius orbit facts for the concrete residue field.

Concrete environment (see S2537):
  A = O_{F'}, C = O_L, K = F', L = L,
  R = O_{F'}[1/10], S = O_L[1/10],
  F = R / p, E = S / P.

The arithmetic q-Frobenius on the residue field at P is

  frobBar y = y ^ Nat.card (R / p)

from S2540.  This file proves:

* frobenius_mem_roots: if g is an irreducible monic polynomial over
  R / p and y is a root of g in S / P, then frobBar y is again
  a root of g;
* natDegree_le_of_frobBar_iterate_fixed: if moreover frobBar^[k] y = y
  with k > 0, then g.natDegree ≤ k;
* frobenius_orbit_card: the orbit of such a root under frobBar has
  cardinality g.natDegree;
* exists_frobBar_iterate_eq_of_mem_rootSet: every root of g in S / P is an
  iterate of frobBar at y.

No sorry, axiom, True/PUnit or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2542ConcreteRootFactorActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
namespace LeanFormal.IUT.XiFPaper.S2543FrobeniusOrbitActual
attribute [local instance] Ideal.Quotient.field
variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
  [Fintype (R ⧸ p)] [Fintype (S ⧸ P)] [DecidableEq (R ⧸ p)] [DecidableEq (S ⧸ P)]

lemma frobBar_eq_frobeniusAlgHom (y : S ⧸ P) :
    frobBar (p := p) (P := P) y =
      FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P) y := by
  rw [FiniteField.coe_frobeniusAlgHom, frobBar, Nat.card_eq_fintype_card]

lemma frobBar_iterate (k : ℕ) (y : S ⧸ P) :
    (frobBar (p := p) (P := P))^[k] y = y ^ (Nat.card (R ⧸ p) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, frobBar, ← pow_mul, Nat.pow_succ]

/-- The arithmetic Frobenius maps a root of an irreducible monic polynomial
over the residue field to another root of the same polynomial. -/
theorem frobenius_mem_roots
    (g : (R ⧸ p)[X]) (hgirr : Irreducible g) (hgmonic : g.Monic)
    (y : S ⧸ P) (hy : y ∈ g.rootSet (S ⧸ P)) :
    frobBar (p := p) (P := P) y ∈ g.rootSet (S ⧸ P) := by
  rw [Polynomial.mem_rootSet'] at hy ⊢
  refine ⟨hy.1, ?_⟩
  have h := Polynomial.aeval_algHom_apply
    (FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P)) y g
  rw [hy.2, map_zero] at h
  have hfrob : FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P) y =
      frobBar (p := p) (P := P) y :=
    (frobBar_eq_frobeniusAlgHom (p := p) (P := P) y).symm
  simpa [hfrob] using h

/-- Every iterate of a root of g under the arithmetic Frobenius is a root of g. -/
lemma frobBar_iterate_mem_rootSet
    (g : (R ⧸ p)[X]) (hgirr : Irreducible g) (hgmonic : g.Monic)
    (y : S ⧸ P) (hy : y ∈ g.rootSet (S ⧸ P)) (k : ℕ) :
    (frobBar (p := p) (P := P))^[k] y ∈ g.rootSet (S ⧸ P) := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact frobenius_mem_roots (p := p) (P := P) g hgirr hgmonic _ ih

/-- If a root y of an irreducible monic polynomial g over R / p is fixed
by the k-th arithmetic Frobenius iterate (with k > 0), then deg g ≤ k. -/
theorem natDegree_le_of_frobBar_iterate_fixed
    (g : (R ⧸ p)[X]) (hgirr : Irreducible g) (hgmonic : g.Monic)
    (y : S ⧸ P) (hy : y ∈ g.rootSet (S ⧸ P))
    {k : ℕ} (hk : 0 < k)
    (hfix : (frobBar (p := p) (P := P))^[k] y = y) :
    g.natDegree ≤ k := by
  classical
  have hy' := hy
  rw [Polynomial.mem_rootSet'] at hy'
  have hint : IsIntegral (R ⧸ p) y := ⟨g, hgmonic, hy'.2⟩
  have hmin : g = minpoly (R ⧸ p) y :=
    minpoly.eq_of_irreducible_of_monic hgirr hy'.2 hgmonic
  have hfun : (frobBar (p := p) (P := P)) =
      ⇑(FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P)) :=
    funext (frobBar_eq_frobeniusAlgHom (p := p) (P := P))
  have hψy : (FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P) ^ k) y = y := by
    rw [AlgHom.coe_pow, ← hfun]
    exact hfix
  have hψformula : ∀ z : S ⧸ P,
      (FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P) ^ k) z =
        z ^ (Nat.card (R ⧸ p) ^ k) := by
    intro z
    rw [AlgHom.coe_pow, ← hfun]
    exact frobBar_iterate (p := p) (P := P) k z
  have hfixEx : ∀ z ∈ IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)),
      (FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P) ^ k) z = z := by
    intro z hz
    refine IntermediateField.adjoin_induction (F := R ⧸ p) (s := ({y} : Set (S ⧸ P)))
      (p := fun z _ => (FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P) ^ k) z = z)
      ?_ ?_ ?_ ?_ ?_ hz
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hψy
    · intro a
      simp
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]
    · intro a _ ha
      rw [map_inv₀, ha]
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]
  have hsubset : (IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) : Set (S ⧸ P)) ⊆
      {z : S ⧸ P | z ^ (Nat.card (R ⧸ p) ^ k) = z} := by
    intro z hz
    have hz' := hfixEx z hz
    rwa [hψformula z] at hz'
  have hq : 2 ≤ Nat.card (R ⧸ p) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hm : 2 ≤ Nat.card (R ⧸ p) ^ k := by
    have h1 : 1 < Nat.card (R ⧸ p) := hq
    have h2 : 1 < Nat.card (R ⧸ p) ^ k := Nat.one_lt_pow (Nat.ne_of_gt hk) h1
    omega
  have hbound : Set.ncard {z : S ⧸ P | z ^ (Nat.card (R ⧸ p) ^ k) = z} ≤
      Nat.card (R ⧸ p) ^ k := by
    set m : ℕ := Nat.card (R ⧸ p) ^ k with hm_def
    have hm2 : 2 ≤ m := hm
    have hpne : (Polynomial.X ^ m - Polynomial.X : (S ⧸ P)[X]) ≠ 0 := by
      intro h
      have hdeg : (Polynomial.X ^ m - Polynomial.X : (S ⧸ P)[X]).natDegree = m := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
        · rw [Polynomial.natDegree_X_pow]
        · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
          omega
      rw [h, Polynomial.natDegree_zero] at hdeg
      omega
    have hset : {z : S ⧸ P | z ^ m = z} =
        ((Polynomial.X ^ m - Polynomial.X : (S ⧸ P)[X]).roots.toFinset : Set (S ⧸ P)) := by
      ext z
      rw [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset,
        Polynomial.mem_roots hpne]
      simp [Polynomial.IsRoot, sub_eq_zero]
    rw [hset, Set.ncard_coe_finset]
    calc ((Polynomial.X ^ m - Polynomial.X : (S ⧸ P)[X]).roots.toFinset).card
        ≤ (Polynomial.X ^ m - Polynomial.X : (S ⧸ P)[X]).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ m - Polynomial.X : (S ⧸ P)[X]).natDegree :=
          Polynomial.card_roots' _
      _ ≤ m := by
          rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          · rw [Polynomial.natDegree_X_pow]
          · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
            omega
  have hcard_le : Nat.card ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) :
      Set (S ⧸ P)) ≤ Nat.card (R ⧸ p) ^ k := by
    calc Nat.card ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) : Set (S ⧸ P))
        = Set.ncard (IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) :
            Set (S ⧸ P)) := Nat.card_coe_set_eq _
      _ ≤ Set.ncard {z : S ⧸ P | z ^ (Nat.card (R ⧸ p) ^ k) = z} :=
          Set.ncard_le_ncard hsubset
      _ ≤ Nat.card (R ⧸ p) ^ k := hbound
  have hmain : Nat.card (R ⧸ p) ^ g.natDegree ≤ Nat.card (R ⧸ p) ^ k := by
    have hMod : Fintype.card ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) :
        Set (S ⧸ P)) = Fintype.card (R ⧸ p) ^ Module.finrank (R ⧸ p)
          ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) : Set (S ⧸ P)) :=
      Module.card_eq_pow_finrank
    have h2 : Module.finrank (R ⧸ p)
        ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) : Set (S ⧸ P)) =
        (minpoly (R ⧸ p) y).natDegree :=
      IntermediateField.adjoin.finrank hint
    calc Nat.card (R ⧸ p) ^ g.natDegree
        = Nat.card (R ⧸ p) ^ (minpoly (R ⧸ p) y).natDegree := by rw [hmin]
      _ = Nat.card (R ⧸ p) ^ Module.finrank (R ⧸ p)
            ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) : Set (S ⧸ P)) := by
          rw [h2]
      _ = Fintype.card (R ⧸ p) ^ Module.finrank (R ⧸ p)
            ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) : Set (S ⧸ P)) := by
          rw [Nat.card_eq_fintype_card]
      _ = Fintype.card ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) :
            Set (S ⧸ P)) := hMod.symm
      _ = Nat.card ↥(IntermediateField.adjoin (R ⧸ p) ({y} : Set (S ⧸ P)) :
            Set (S ⧸ P)) := (Nat.card_eq_fintype_card).symm
      _ ≤ Nat.card (R ⧸ p) ^ k := hcard_le
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card (R ⧸ p))).mp hmain

/-- The first n iterates of y under the arithmetic Frobenius, as a finset. -/
noncomputable def frobOrbit (y : S ⧸ P) (n : ℕ) : Finset (S ⧸ P) :=
  (Finset.range n).image (fun k => (frobBar (p := p) (P := P))^[k] y)

/-- The orbit of a root y of an irreducible monic g under the arithmetic
Frobenius has cardinality g.natDegree. -/
theorem frobenius_orbit_card
    (g : (R ⧸ p)[X]) (hgirr : Irreducible g) (hgmonic : g.Monic)
    (y : S ⧸ P) (hy : y ∈ g.rootSet (S ⧸ P)) :
    (frobOrbit (p := p) (P := P) y g.natDegree).card = g.natDegree := by
  classical
  have hno : ∀ a b : ℕ, a < b → b < g.natDegree →
      (frobBar (p := p) (P := P))^[a] y = (frobBar (p := p) (P := P))^[b] y → False := by
    intro a b hab hbd heq
    have hk : 0 < b - a := Nat.sub_pos_of_lt hab
    have hsplit : (frobBar (p := p) (P := P))^[b] y =
        (frobBar (p := p) (P := P))^[a] ((frobBar (p := p) (P := P))^[b - a] y) := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hab)]
    have heq' : (frobBar (p := p) (P := P))^[a] y =
        (frobBar (p := p) (P := P))^[a] ((frobBar (p := p) (P := P))^[b - a] y) := by
      rw [← hsplit]
      exact heq
    have hyfix : (frobBar (p := p) (P := P))^[b - a] y = y :=
      ((frobBar_injective (p := p) (P := P)).iterate a heq').symm
    have hle := natDegree_le_of_frobBar_iterate_fixed (p := p) (P := P)
      g hgirr hgmonic y hy hk hyfix
    omega
  have hinj : Set.InjOn (fun k => (frobBar (p := p) (P := P))^[k] y)
      ↑(Finset.range g.natDegree) := by
    intro a ha b hb hab
    have ha' : a < g.natDegree := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < g.natDegree := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exfalso
      exact hno a b hlt hb' hab
    · exact heq
    · exfalso
      exact hno b a hgt ha' hab.symm
  rw [frobOrbit, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Every root of g in S / P is an iterate of the arithmetic Frobenius at y. -/
theorem exists_frobBar_iterate_eq_of_mem_rootSet
    (g : (R ⧸ p)[X]) (hgirr : Irreducible g) (hgmonic : g.Monic)
    (y : S ⧸ P) (hy : y ∈ g.rootSet (S ⧸ P))
    (z : S ⧸ P) (hz : z ∈ g.rootSet (S ⧸ P)) :
    ∃ k, k < g.natDegree ∧ (frobBar (p := p) (P := P))^[k] y = z := by
  classical
  have hsub : (frobOrbit (p := p) (P := P) y g.natDegree : Set (S ⧸ P)) ⊆
      g.rootSet (S ⧸ P) := by
    intro w hw
    rw [Finset.mem_coe, frobOrbit] at hw
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw
    exact frobBar_iterate_mem_rootSet (p := p) (P := P) g hgirr hgmonic y hy k
  have hcard := frobenius_orbit_card (p := p) (P := P) g hgirr hgmonic y hy
  have hEq : (frobOrbit (p := p) (P := P) y g.natDegree : Set (S ⧸ P)) =
      g.rootSet (S ⧸ P) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    calc (g.rootSet (S ⧸ P)).ncard ≤ g.natDegree := Polynomial.ncard_rootSet_le g _
      _ = (frobOrbit (p := p) (P := P) y g.natDegree).card := hcard.symm
      _ = (frobOrbit (p := p) (P := P) y g.natDegree : Set (S ⧸ P)).ncard :=
          (Set.ncard_coe_finset _).symm
  have hz' : z ∈ (frobOrbit (p := p) (P := P) y g.natDegree : Set (S ⧸ P)) := by
    rw [hEq]
    exact hz
  rw [Finset.mem_coe, frobOrbit] at hz'
  obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz'
  exact ⟨k, Finset.mem_range.mp hk, hkz⟩

#print axioms frobenius_mem_roots
#print axioms natDegree_le_of_frobBar_iterate_fixed
#print axioms frobenius_orbit_card
#print axioms exists_frobBar_iterate_eq_of_mem_rootSet
end LeanFormal.IUT.XiFPaper.S2543FrobeniusOrbitActual
end
