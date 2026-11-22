import LeanFormal.IUT.Foundations.AlgebraicGeometry.OrbitNonvanishingLemma
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite G-stable principal affine refinement

Let B be a commutative ring with a finite group G acting by ring automorphisms,
and let W = Spec B.  For a finite open cover of W by complements of closed sets
V(J_j), this file proves the existence of a finite cover of W by principal
G-stable affine opens D(H), each contained in one of the given open sets.

The proof follows the vanishing-ideal route: for a point x choose an open set
O_j containing it, let C_j = V(J_j) and I = vanishingIdeal C_j.  The finite
G-orbit of x lies in O_j, so I is not contained in the union of the maximal
ideals of the orbit; prime avoidance gives f in I outside all of them.  Then
H = product over g of (g . f) is a G-invariant section, D(H) is a principal
G-stable open contained in O_j and containing x.  Quasi-compactness of W gives
a finite subcover.
-/

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteGStableAffineRefinement

universe u

variable {B : Type u} [CommRing B]
variable {G : Type u} [Group G] [MulSemiringAction G B] [Fintype G]

/-- The topological space W = Spec B. -/
abbrev W := PrimeSpectrum B

/-- The point action on Spec B induced by the ring action. -/
noncomputable def pointImage (g : G) (x : W (B := B)) : W (B := B) :=
  ⟨Ideal.map (MulSemiringAction.toRingEquiv G B g).toRingHom x.asIdeal,
    Ideal.map_isPrime_of_surjective (MulSemiringAction.toRingEquiv G B g).surjective
      (by simp)⟩

/-- The principal open D(f). -/
def D (f : B) : Set (W (B := B)) :=
  PrimeSpectrum.basicOpen f

/-- The finite orbit of a point, including the point itself. -/
noncomputable def orbit (x : W (B := B)) : Finset (W (B := B)) := by
  classical
  exact insert x ((Finset.univ : Finset G).image (fun g => pointImage g x))

/-- The section f is nonzero at the point x iff x lies in D(f). -/
theorem mem_D_iff (f : B) (x : W (B := B)) :
    x ∈ D f ↔ f ∉ x.asIdeal := by
  rw [D]
  rfl

/-- Membership in the image point: f lies in the image ideal iff the inverse
translate of f lies in the original ideal. -/
theorem mem_pointImage_iff (g : G) (x : W (B := B)) (f : B) :
    f ∈ (pointImage g x).asIdeal ↔ (g⁻¹ • f) ∈ x.asIdeal := by
  rw [pointImage]
  change f ∈ Ideal.map (MulSemiringAction.toRingEquiv G B g).toRingHom x.asIdeal ↔
    (g⁻¹ : G) • f ∈ x.asIdeal
  rw [Ideal.mem_map_iff_of_surjective (f := (MulSemiringAction.toRingEquiv G B g).toRingHom)
    (MulSemiringAction.toRingEquiv G B g).surjective]
  constructor
  · rintro ⟨a, ha, hfa⟩
    rw [← hfa]
    simpa using ha
  · intro h
    exact ⟨(g⁻¹ : G) • f, h, by simp⟩

/-- The orbit consists of points obtained by the point action, plus the point. -/
theorem mem_orbit (x : W (B := B)) (y : W (B := B)) :
    y ∈ orbit (G := G) x ↔ y = x ∨ ∃ g : G, pointImage g x = y := by
  classical
  rw [orbit]
  constructor
  · intro hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact Or.inl h
    · obtain ⟨g, -, hg⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨g, hg⟩
  · intro hy
    rcases hy with rfl | ⟨g, rfl⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩)

/-- The orbit product H = product over g of (g . f). -/
noncomputable def orbitProduct (f : B) : B :=
  ∏ g : G, g • f

/-- The orbit product is G-invariant. -/
theorem orbitProduct_smul (f : B) (g : G) :
    g • orbitProduct (G := G) f = orbitProduct (G := G) f := by
  classical
  rw [orbitProduct]
  change MulSemiringAction.toRingHom G B g (∏ h : G, h • f) = ∏ h : G, h • f
  rw [map_prod]
  change (∏ h : G, g • (h • f)) = ∏ h : G, h • f
  refine Finset.prod_bij (fun h _ => g * h) ?_ ?_ ?_ ?_
  · intro h hh; exact Finset.mem_univ _
  · intro h1 h2 _ _ h; exact mul_left_cancel h
  · intro h hh; exact ⟨g⁻¹ * h, Finset.mem_univ _, by simp⟩
  · intro h hh; rw [mul_smul]


/-- The principal open of an image point: y lies in D(f) after applying g iff
the inverse translate of y lies in D(g^{-1} . f). -/
theorem pointImage_mem_D_iff (g : G) (x : W (B := B)) (f : B) :
    pointImage g x ∈ D f ↔ x ∈ D ((g⁻¹ : G) • f) := by
  rw [mem_D_iff, mem_D_iff, mem_pointImage_iff]

/-- The point image is a group action. -/
theorem pointImage_mul (g h : G) (x : W (B := B)) :
    pointImage g (pointImage h x) = pointImage (g * h) x := by
  rw [PrimeSpectrum.ext_iff]
  change Ideal.map (MulSemiringAction.toRingEquiv G B g).toRingHom
      (Ideal.map (MulSemiringAction.toRingEquiv G B h).toRingHom x.asIdeal) =
    Ideal.map (MulSemiringAction.toRingEquiv G B (g * h)).toRingHom x.asIdeal
  rw [Ideal.map_map]
  congr 1
  ext b
  simp [mul_smul]

/-- The identity point image is the identity. -/
theorem pointImage_one (x : W (B := B)) : pointImage (G := G) 1 x = x := by
  rw [PrimeSpectrum.ext_iff]
  change Ideal.map (MulSemiringAction.toRingEquiv G B 1).toRingHom x.asIdeal = x.asIdeal
  rw [show (MulSemiringAction.toRingEquiv G B 1).toRingHom = RingHom.id B by
    ext b
    simp]
  exact Ideal.map_id x.asIdeal

/-- If f lies in a prime ideal then the orbit product lies in it. -/
theorem orbitProduct_mem_of_mem {p : Ideal B} (hp : p.IsPrime) {f : B} (hf : f ∈ p) :
    orbitProduct (G := G) f ∈ p := by
  classical
  rw [orbitProduct]
  simpa using Ideal.prod_mem p (Finset.mem_univ (1 : G)) (by simpa using hf)

/-- The vanishing ideal of V(J) has the same zero locus as J. -/
theorem zeroLocus_vanishingIdeal_eq (J : Ideal B) :
    PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal
        (PrimeSpectrum.zeroLocus (J : Set B)) : Set B) =
      PrimeSpectrum.zeroLocus (J : Set B) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PrimeSpectrum.mem_zeroLocus] at hx ⊢
    exact le_trans (PrimeSpectrum.le_vanishingIdeal_zeroLocus J) hx
  · exact PrimeSpectrum.subset_zeroLocus_vanishingIdeal _

/-- Pointwise principal orbit-stable refinement: if x is in the open complement
of V(J) and the orbit stays in that complement, there is H with x in D(H),
D(H) inside the complement, and D(H) G-stable. -/
theorem exists_principal_orbit_stable_inside
    (J : Ideal B) (x : W (B := B))
    (hx : x ∉ PrimeSpectrum.zeroLocus (J : Set B))
    (hstable : ∀ g : G, pointImage g x ∉ PrimeSpectrum.zeroLocus (J : Set B)) :
    ∃ H : B, x ∈ D H ∧
      D H ⊆ (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ∧
      (∀ g : G, pointImage g '' D H = D H) ∧
      (∀ g : G, g • H = H) := by
  classical
  let C := PrimeSpectrum.zeroLocus (J : Set B)
  let I := PrimeSpectrum.vanishingIdeal C
  have hC : PrimeSpectrum.zeroLocus (I : Set B) = C := by
    dsimp [C, I]
    exact zeroLocus_vanishingIdeal_eq J
  have hx_not : x ∉ PrimeSpectrum.zeroLocus (I : Set B) := by
    rw [hC]; exact hx
  have hnot_le : ¬ I ≤ x.asIdeal := by
    intro hle
    exact hx_not ((PrimeSpectrum.mem_zeroLocus _ _).mpr hle)
  have horbit_not : ∀ y ∈ orbit (G := G) x, y ∉ C := by
    intro y hy hyC
    rw [mem_orbit] at hy
    rcases hy with rfl | ⟨g, rfl⟩
    · exact hx hyC
    · exact hstable g hyC
  have hnot_union : ¬ ((I : Ideal B) : Set B) ⊆
      ⋃ y ∈ (orbit (G := G) x : Set (W (B := B))), (y.asIdeal : Set B) := by
    intro hsub
    have hprime : ∀ y ∈ orbit (G := G) x, y.asIdeal.IsPrime :=
      fun y hy => y.isPrime
    have hiff := (Ideal.subset_union_prime (R := B) (s := orbit (G := G) x)
      (f := fun y : W (B := B) => y.asIdeal) (a := x) (b := x)
      (fun y hy _ _ => hprime y hy)).1 hsub
    obtain ⟨y, hy, hIle⟩ := hiff
    have hyC : y ∈ C := by
      rw [← hC]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hIle
    exact horbit_not y hy hyC
  obtain ⟨f, hfI, hfnot⟩ := Set.not_subset.1 hnot_union
  have hf_out : ∀ y ∈ orbit (G := G) x, f ∉ y.asIdeal := by
    intro y hy hmem
    exact hfnot (Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hmem⟩⟩)
  let H := orbitProduct (G := G) f
  have hxH : x ∈ D H := by
    rw [mem_D_iff]
    intro hmem
    rw [show H = orbitProduct (G := G) f from rfl, orbitProduct] at hmem
    rw [Ideal.IsPrime.prod_mem_iff] at hmem
    obtain ⟨g, -, hg⟩ := hmem
    have hginv : pointImage (g⁻¹) x ∈ orbit (G := G) x := by
      rw [mem_orbit]
      exact Or.inr ⟨g⁻¹, rfl⟩
    exact hf_out (pointImage (g⁻¹) x) hginv
      ((mem_pointImage_iff (G := G) (g⁻¹) x f).mpr (by simpa using hg))
  have hDH_subset : D H ⊆ Cᶜ := by
    intro p hp hpC
    have hfp : f ∈ p.asIdeal :=
      (PrimeSpectrum.mem_vanishingIdeal C f).mp hfI p hpC
    have hHp : H ∈ p.asIdeal := by
      dsimp [H]
      exact orbitProduct_mem_of_mem (G := G) p.isPrime hfp
    exact (mem_D_iff H p).mp hp hHp
  have hDH_stable : ∀ g : G, pointImage g '' D H = D H := by
    intro g
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [pointImage_mem_D_iff]
      rw [orbitProduct_smul]
      exact hz
    · intro hy
      refine ⟨pointImage (g⁻¹) y, ?_, ?_⟩
      · rw [pointImage_mem_D_iff]
        rw [orbitProduct_smul]
        exact hy
      · rw [pointImage_mul, mul_inv_cancel, pointImage_one]
  exact ⟨H, hxH, fun p hp => hDH_subset hp, hDH_stable, orbitProduct_smul (G := G) f⟩

/-- The main finite G-stable principal refinement theorem for a finite open
cover by complements of zero loci. -/
theorem finite_gStable_principal_refinement
    {J : Type u} [Fintype J]
    (Jideal : J → Ideal B)
    (hcover : ∀ x : W (B := B), ∃ j : J, x ∉ PrimeSpectrum.zeroLocus (Jideal j : Set B))
    (hstable : ∀ (j : J) (g : G) (x : W (B := B)),
      x ∉ PrimeSpectrum.zeroLocus (Jideal j : Set B) →
        pointImage g x ∉ PrimeSpectrum.zeroLocus (Jideal j : Set B)) :
    ∃ (K : Finset (W (B := B))) (H : W (B := B) → B) (j : W (B := B) → J),
      (∀ k ∈ K, D (H k) ⊆ (PrimeSpectrum.zeroLocus (Jideal (j k) : Set B))ᶜ) ∧
      (∀ k ∈ K, ∀ g : G, pointImage g '' D (H k) = D (H k)) ∧
      (∀ k ∈ K, ∀ g : G, g • H k = H k) ∧
      (∀ x : W (B := B), ∃ k ∈ K, x ∈ D (H k)) := by
  classical
  let Hfun : W (B := B) → B := fun x =>
    Classical.choose (exists_principal_orbit_stable_inside (G := G)
      (J := Jideal (Classical.choose (hcover x))) x
      (Classical.choose_spec (hcover x))
      (fun g => hstable (Classical.choose (hcover x)) g x
        (Classical.choose_spec (hcover x))))
  let jfun : W (B := B) → J := fun x => Classical.choose (hcover x)
  have hHfun : ∀ x : W (B := B), x ∈ D (Hfun x) := fun x =>
    (Classical.choose_spec (exists_principal_orbit_stable_inside (G := G)
      (J := Jideal (jfun x)) x (Classical.choose_spec (hcover x))
      (fun g => hstable (jfun x) g x (Classical.choose_spec (hcover x))))).1
  have hUopen : ∀ x : W (B := B), IsOpen (D (Hfun x)) := fun x => PrimeSpectrum.isOpen_basicOpen
  have hcoverU : (Set.univ : Set (W (B := B))) ⊆ ⋃ x, D (Hfun x) := by
    intro x _; exact Set.mem_iUnion.2 ⟨x, hHfun x⟩
  obtain ⟨K, hK⟩ := isCompact_univ.elim_finite_subcover (fun x => D (Hfun x)) hUopen hcoverU
  refine ⟨K, Hfun, jfun, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact (Classical.choose_spec (exists_principal_orbit_stable_inside (G := G)
      (J := Jideal (jfun k)) k (Classical.choose_spec (hcover k))
      (fun g => hstable (jfun k) g k (Classical.choose_spec (hcover k))))).2.1
  · intro k hk g
    exact (Classical.choose_spec (exists_principal_orbit_stable_inside (G := G)
      (J := Jideal (jfun k)) k (Classical.choose_spec (hcover k))
      (fun g => hstable (jfun k) g k (Classical.choose_spec (hcover k))))).2.2.1 g
  · intro k hk g
    exact (Classical.choose_spec (exists_principal_orbit_stable_inside (G := G)
      (J := Jideal (jfun k)) k (Classical.choose_spec (hcover k))
      (fun g => hstable (jfun k) g k (Classical.choose_spec (hcover k))))).2.2.2 g
  · intro x
    have hx := hK (Set.mem_univ x)
    rw [Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    rw [Set.mem_iUnion] at hk
    obtain ⟨hkK, hxD⟩ := hk
    exact ⟨k, hkK, hxD⟩


/-- The point itself lies in its orbit. -/
theorem mem_orbit_self (x : W (B := B)) : x ∈ orbit (G := G) x := by
  rw [mem_orbit]
  exact Or.inl rfl

/-- The orbit product is invariant under the point action, in D-form. -/
theorem D_orbitProduct_smul (f : B) (g : G) :
    D (g • orbitProduct (G := G) f) = D (orbitProduct (G := G) f) := by
  rw [orbitProduct_smul]

/-- If f vanishes on a closed set C, then D(f) is contained in the complement
of C. -/
theorem D_subset_compl_of_mem_vanishingIdeal
    {C : Set (W (B := B))} {f : B}
    (hf : f ∈ PrimeSpectrum.vanishingIdeal C) :
    D f ⊆ Cᶜ := by
  intro p hp hpC
  exact (mem_D_iff f p).mp hp
    ((PrimeSpectrum.mem_vanishingIdeal C f).mp hf p hpC)

/-- The orbit product's principal open is contained in the principal open of
any factor. -/
theorem D_orbitProduct_subset_D_of_isPrime
    (f : B) : D (orbitProduct (G := G) f) ⊆ D f := by
  intro p hp
  rw [mem_D_iff] at hp ⊢
  intro hf
  exact hp (orbitProduct_mem_of_mem (G := G) p.isPrime hf)

/-- The orbit product's principal open is stable under the point action. -/
theorem D_orbitProduct_stable (f : B) (g : G) :
    pointImage g '' D (orbitProduct (G := G) f) = D (orbitProduct (G := G) f) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [pointImage_mem_D_iff]
    rwa [orbitProduct_smul]
  · intro hy
    refine ⟨pointImage (B := B) g⁻¹ y, ?_, ?_⟩
    · rw [pointImage_mem_D_iff]
      rwa [orbitProduct_smul]
    · rw [pointImage_mul, mul_inv_cancel, pointImage_one]

/-- The finite refinement theorem in the point-indexed form. -/
theorem finite_gStable_principal_refinement_pointwise
    {J : Type u} [Fintype J]
    (Jideal : J → Ideal B)
    (hcover : ∀ x : W (B := B), ∃ j : J, x ∉ PrimeSpectrum.zeroLocus (Jideal j : Set B))
    (hstable : ∀ (j : J) (g : G) (x : W (B := B)),
      x ∉ PrimeSpectrum.zeroLocus (Jideal j : Set B) →
        pointImage g x ∉ PrimeSpectrum.zeroLocus (Jideal j : Set B)) :
    ∃ (K : Finset (W (B := B))) (H : W (B := B) → B) (j : W (B := B) → J),
      (∀ k ∈ K, D (H k) ⊆ (PrimeSpectrum.zeroLocus (Jideal (j k) : Set B))ᶜ) ∧
      (∀ k ∈ K, ∀ g : G, pointImage g '' D (H k) = D (H k)) ∧
      (∀ k ∈ K, ∀ g : G, g • H k = H k) ∧
      (∀ x : W (B := B), ∃ k ∈ K, x ∈ D (H k)) :=
  finite_gStable_principal_refinement (G := G) Jideal hcover hstable

end LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteGStableAffineRefinement
