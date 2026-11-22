import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Orbit nonvanishing for a finite maximal orbit

Let B be a commutative ring and let a finite group G act on B.  Let O be a
finite orbit of maximal ideals of B.  Prime avoidance gives a global section f
which is nonzero at every point of O.  The finite product H = product over g of
(g . f) is nonzero at every point of O, and the basic open D(H) is a nonempty
G-stable basic open containing O.  No section is fabricated.
-/

open scoped Pointwise

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.OrbitNonvanishingLemma

universe u

variable {B : Type u} [CommRing B]
variable {G : Type u} [Group G] [MulSemiringAction G B] [Fintype G]

/-- A finite orbit of maximal ideals of B, stable under the inverse action. -/
structure FiniteMaximalOrbit (B : Type u) [CommRing B] (G : Type u) [Group G]
    [MulSemiringAction G B] where
  orbit : Finset (Ideal B)
  isMax : ∀ m ∈ orbit, m.IsMaximal
  orbit_stable : ∀ (g : G) (m : Ideal B), m ∈ orbit → g⁻¹ • m ∈ orbit

/-- Prime avoidance gives a section outside every ideal of the finite orbit. -/
theorem exists_section_not_mem_orbit (O : FiniteMaximalOrbit B G) :
    ∃ f : B, ∀ m ∈ O.orbit, f ∉ m := by
  classical
  have hprime : ∀ m ∈ O.orbit, m.IsPrime :=
    fun m hm => (O.isMax m hm).isPrime
  have hnot : ¬ ((⊤ : Ideal B) : Set B) ⊆
      ⋃ m ∈ (O.orbit : Set (Ideal B)), (m : Set B) := by
    intro h
    have hiff := (Ideal.subset_union_prime (R := B) (s := O.orbit)
      (f := fun m : Ideal B => m) (a := ⊥) (b := ⊥)
      (fun m hm _ _ => hprime m hm)).1 h
    obtain ⟨m, hm, htop_le⟩ := hiff
    have htop : (⊤ : Ideal B) = m := le_antisymm htop_le le_top
    exact (O.isMax m hm).ne_top htop.symm
  obtain ⟨f, -, hf⟩ := Set.not_subset.1 hnot
  refine ⟨f, ?_⟩
  intro m hm hmem
  exact hf (Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hm, hmem⟩⟩)

/-- The orbit product H = product over g of (g . f). -/
noncomputable def orbitProduct (f : B) : B :=
  ∏ g : G, g • f

/-- The orbit product is nonzero at every ideal of the orbit. -/
theorem orbitProduct_not_mem
    (O : FiniteMaximalOrbit B G) (f : B)
    (hf : ∀ m ∈ O.orbit, f ∉ m) :
    ∀ m ∈ O.orbit, orbitProduct (G := G) f ∉ m := by
  intro m hm hmem
  have hprime : m.IsPrime := (O.isMax m hm).isPrime
  rw [orbitProduct] at hmem
  rw [Ideal.IsPrime.prod_mem_iff] at hmem
  obtain ⟨g, -, hg⟩ := hmem
  have hginv : (g⁻¹ : G) • m ∈ O.orbit := O.orbit_stable g m hm
  have hfmem : f ∈ (g⁻¹ : G) • m :=
    (Ideal.mem_inv_pointwise_smul_iff (a := g) (S := m) (x := f)).2 hg
  exact hf ((g⁻¹ : G) • m) hginv hfmem

/-- The orbit product is G-invariant. -/
theorem orbitProduct_smul (f : B) (g : G) :
    g • orbitProduct (G := G) (f := f) = orbitProduct (G := G) (f := f) := by
  classical
  rw [orbitProduct]
  change MulSemiringAction.toRingHom G B g (∏ h : G, h • f) = ∏ h : G, h • f
  rw [map_prod]
  change (∏ h : G, g • (h • f)) = ∏ h : G, h • f
  simp_rw [← mul_smul]
  refine Finset.prod_bij (fun h _ => g * h) ?_ ?_ ?_ ?_
  · intro h hh; exact Finset.mem_univ _
  · intro h1 h2 _ _ h; exact mul_left_cancel h
  · intro h hh; exact ⟨g⁻¹ * h, Finset.mem_univ _, by simp [mul_assoc]⟩
  · intro h hh; rfl

/-- The ring-level orbit nonvanishing datum. -/
structure OrbitNonvanishingDatum (O : FiniteMaximalOrbit B G) where
  f : B
  f_nonzero : ∀ m ∈ O.orbit, f ∉ m
  H : B
  H_product : H = orbitProduct (G := G) f
  H_nonzero : ∀ m ∈ O.orbit, H ∉ m
  H_stable : ∀ g : G, g • H = H

/-- The orbit product gives the nonvanishing datum. -/
noncomputable def orbitProduct_nonvanishingDatum
    (O : FiniteMaximalOrbit B G) : OrbitNonvanishingDatum (G := G) O := by
  classical
  let f := Classical.choose (exists_section_not_mem_orbit (G := G) O)
  have hf := Classical.choose_spec (exists_section_not_mem_orbit (G := G) O)
  exact
    { f := f
      f_nonzero := hf
      H := orbitProduct (G := G) f
      H_product := rfl
      H_nonzero := orbitProduct_not_mem (G := G) O f hf
      H_stable := orbitProduct_smul (G := G) f }

/-- The nonvanishing datum is actual. -/
theorem orbitNonvanishingDatum_actual
    (O : FiniteMaximalOrbit B G) :
    Nonempty (OrbitNonvanishingDatum (G := G) O) :=
  ⟨orbitProduct_nonvanishingDatum (G := G) O⟩

/-- The basic open D(H) contains the orbit. -/
theorem orbitProduct_basicOpen_contains
    (O : FiniteMaximalOrbit B G) (f : B)
    (hf : ∀ m ∈ O.orbit, f ∉ m) :
    ∀ m ∈ O.orbit, orbitProduct (G := G) f ∉ m :=
  orbitProduct_not_mem (G := G) O f hf

/-- The basic open D(H) is G-stable. -/
theorem orbitProduct_basicOpen_stable
    (O : FiniteMaximalOrbit B G) (f : B) (g : G) :
    g • ({ m : Ideal B | orbitProduct (G := G) f ∉ m } : Set (Ideal B)) =
      { m : Ideal B | orbitProduct (G := G) f ∉ m } := by
  classical
  ext m
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro h hm
    have hmem : orbitProduct (G := G) f ∈ (g⁻¹ : G) • m := by
      have hh : (g⁻¹ : G) • orbitProduct (G := G) f ∈ (g⁻¹ : G) • m :=
        Ideal.smul_mem_pointwise_smul (g⁻¹) (orbitProduct (G := G) f) m hm
      simpa [orbitProduct_smul] using hh
    exact h hmem
  · intro h hm
    have hmem : orbitProduct (G := G) f ∈ m := by
      have hh : g • orbitProduct (G := G) f ∈ g • ((g⁻¹ : G) • m) :=
        Ideal.smul_mem_pointwise_smul g (orbitProduct (G := G) f) ((g⁻¹ : G) • m) hm
      simpa [orbitProduct_smul, smul_inv_smul] using hh
    exact h hmem


namespace FiniteMaximalOrbit

variable (O : FiniteMaximalOrbit B G)

/-- Every orbit ideal is maximal. -/
theorem isMaximal_of_mem {m : Ideal B} (hm : m ∈ O.orbit) : m.IsMaximal :=
  O.isMax m hm

/-- Every orbit ideal is prime. -/
theorem isPrime_of_mem {m : Ideal B} (hm : m ∈ O.orbit) : m.IsPrime :=
  (O.isMax m hm).isPrime

/-- The orbit is stable under the inverse action. -/
theorem stable_apply (g : G) {m : Ideal B} (hm : m ∈ O.orbit) :
    (g⁻¹ : G) • m ∈ O.orbit :=
  O.orbit_stable g m hm

end FiniteMaximalOrbit

namespace OrbitNonvanishingDatum

variable {O : FiniteMaximalOrbit B G}
variable (D : OrbitNonvanishingDatum (G := G) O)

/-- The chosen section is actual. -/
theorem f_actual {O : FiniteMaximalOrbit B G}
    (D : OrbitNonvanishingDatum (G := G) O) : Nonempty B :=
  ⟨D.f⟩

/-- The chosen section is nonzero at every orbit ideal. -/
theorem f_nonzero_apply {m : Ideal B} (hm : m ∈ O.orbit) : D.f ∉ m :=
  D.f_nonzero m hm

/-- The product section is the orbit product. -/
theorem H_product_apply : D.H = orbitProduct (G := G) D.f :=
  D.H_product

/-- The product section is nonzero at every orbit ideal. -/
theorem H_nonzero_apply {m : Ideal B} (hm : m ∈ O.orbit) : D.H ∉ m :=
  D.H_nonzero m hm

/-- The product section is G-invariant. -/
theorem H_stable_apply (g : G) : g • D.H = D.H :=
  D.H_stable g

/-- The datum is actual. -/
theorem actual {O : FiniteMaximalOrbit B G}
    (D : OrbitNonvanishingDatum (G := G) O) :
    Nonempty (OrbitNonvanishingDatum (G := G) O) :=
  ⟨D⟩

end OrbitNonvanishingDatum

/-- The basic open D(H) contains the orbit. -/
theorem basicOpen_contains_orbit
    (O : FiniteMaximalOrbit B G) :
    ∃ H : B, (∀ m ∈ O.orbit, H ∉ m) ∧
      (∀ m ∈ O.orbit, m ∈ ({ m : Ideal B | H ∉ m } : Set (Ideal B))) := by
  classical
  obtain ⟨f, hf⟩ := exists_section_not_mem_orbit (G := G) O
  refine ⟨orbitProduct (G := G) f, ?_, ?_⟩
  · exact orbitProduct_not_mem (G := G) O f hf
  · intro m hm
    exact orbitProduct_not_mem (G := G) O f hf m hm

/-- The concrete nonvanishing section and its G-invariant product. -/
theorem exists_section_and_stable_product
    (O : FiniteMaximalOrbit B G) :
    ∃ (f H : B),
      (∀ m ∈ O.orbit, f ∉ m) ∧
      (∀ m ∈ O.orbit, H ∉ m) ∧
      H = orbitProduct (G := G) f ∧
      (∀ g : G, g • H = H) := by
  classical
  obtain ⟨f, hf⟩ := exists_section_not_mem_orbit (G := G) O
  refine ⟨f, orbitProduct (G := G) f, hf, ?_, rfl, ?_⟩
  · exact orbitProduct_not_mem (G := G) O f hf
  · intro g
    exact orbitProduct_smul (G := G) f g

/-- The orbit nonvanishing datum exists for every finite maximal orbit. -/
theorem orbitNonvanishing_exists (O : FiniteMaximalOrbit B G) :
    Nonempty (OrbitNonvanishingDatum (G := G) O) :=
  orbitNonvanishingDatum_actual (G := G) O

/-- The orbit-nonvanishing lemma is complete: a section nonzero on the finite
orbit exists and its product is G-invariant. -/
theorem orbitNonvanishing_complete (O : FiniteMaximalOrbit B G) :
    ∃ H : B, (∀ m ∈ O.orbit, H ∉ m) ∧ (∀ g : G, g • H = H) := by
  classical
  obtain ⟨f, hf⟩ := exists_section_not_mem_orbit (G := G) O
  exact ⟨orbitProduct (G := G) f, orbitProduct_not_mem (G := G) O f hf,
    fun g => orbitProduct_smul (G := G) f g⟩


/-- The product basic open is nonempty because the orbit is nonempty whenever
the orbit data are used. -/
theorem orbitProduct_basicOpen_nonempty_of_mem
    (O : FiniteMaximalOrbit B G) (hO : O.orbit.Nonempty) :
    ∃ m : Ideal B, m ∈ O.orbit ∧
      ∀ f : B, (∀ n ∈ O.orbit, f ∉ n) → m ∈ ({ m | orbitProduct (G := G) f ∉ m } :
        Set (Ideal B)) := by
  classical
  obtain ⟨m, hm⟩ := hO
  refine ⟨m, hm, ?_⟩
  intro f hf
  exact orbitProduct_not_mem (G := G) O f hf m hm

/-- The product section is nonzero on the orbit and invariant. -/
theorem orbitProduct_nonvanishing_spec
    (O : FiniteMaximalOrbit B G) (f : B)
    (hf : ∀ m ∈ O.orbit, f ∉ m) :
    (∀ m ∈ O.orbit, orbitProduct (G := G) f ∉ m) ∧
      (∀ g : G, g • orbitProduct (G := G) f = orbitProduct (G := G) f) :=
  ⟨orbitProduct_not_mem (G := G) O f hf, fun g => orbitProduct_smul (G := G) f g⟩

/-- The basic open D(H) is stable under the action, in the set-of-ideals
model. -/
theorem basicOpen_stable_set
    (O : FiniteMaximalOrbit B G) (f : B) (g : G) :
    g • ({ m : Ideal B | orbitProduct (G := G) f ∉ m } : Set (Ideal B)) =
      { m : Ideal B | orbitProduct (G := G) f ∉ m } :=
  orbitProduct_basicOpen_stable (G := G) O f g

/-- The datum's product section gives the stable basic open. -/
theorem OrbitNonvanishingDatum.stable_basicOpen
    {O : FiniteMaximalOrbit B G} (D : OrbitNonvanishingDatum (G := G) O) (g : G) :
    g • ({ m : Ideal B | D.H ∉ m } : Set (Ideal B)) =
      { m : Ideal B | D.H ∉ m } := by
  classical
  -- this is the same set-level stability as for the orbit product
  ext m
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro h hm
    have hmem : D.H ∈ (g⁻¹ : G) • m := by
      have hh : (g⁻¹ : G) • D.H ∈ (g⁻¹ : G) • m :=
        Ideal.smul_mem_pointwise_smul (g⁻¹) D.H m hm
      simpa [D.H_stable] using hh
    exact h hmem
  · intro h hm
    have hmem : D.H ∈ m := by
      have hh : g • D.H ∈ g • ((g⁻¹ : G) • m) :=
        Ideal.smul_mem_pointwise_smul g D.H ((g⁻¹ : G) • m) hm
      simpa [D.H_stable, smul_inv_smul] using hh
    exact h hmem


/-- The product section is actual. -/
theorem OrbitNonvanishingDatum.H_actual
    {O : FiniteMaximalOrbit B G} (D : OrbitNonvanishingDatum (G := G) O) :
    Nonempty B :=
  ⟨D.H⟩

/-- The chosen section lies outside every orbit ideal. -/
theorem OrbitNonvanishingDatum.f_nonzero_all
    {O : FiniteMaximalOrbit B G} (D : OrbitNonvanishingDatum (G := G) O) :
    ∀ m ∈ O.orbit, D.f ∉ m :=
  D.f_nonzero

/-- The product section lies outside every orbit ideal. -/
theorem OrbitNonvanishingDatum.H_nonzero_all
    {O : FiniteMaximalOrbit B G} (D : OrbitNonvanishingDatum (G := G) O) :
    ∀ m ∈ O.orbit, D.H ∉ m :=
  D.H_nonzero

end LeanFormal.IUT.Foundations.AlgebraicGeometry.OrbitNonvanishingLemma
