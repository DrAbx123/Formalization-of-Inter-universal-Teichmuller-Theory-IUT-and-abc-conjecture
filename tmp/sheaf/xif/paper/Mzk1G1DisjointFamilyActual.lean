import tmp.sheaf.xif.paper.Mzk1G1FiniteDisjointBelyiActual
import tmp.sheaf.xif.paper.Mzk1G1KvCompactActual
import Mathlib.Topology.Order.Compact
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic

set_option relaxedAutoImplicit false
noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1FiniteDisjointBelyiActual
open LeanFormal.IUT.XiFPaper.G1KvCompactActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Combinatorial core of section 7.3: at most r points cannot meet all r+1 boundaries -/

/-- Route 7.3 (E1): given r + 1 pairwise disjoint boundaries, any set of at
most r points is missed by at least one of them.  This is the counting
argument that produces a map phi_i avoiding a given tuple of points. -/
theorem exists_boundary_avoiding {α : Type*} {r : ℕ} {E : Fin (r + 1) → Set α}
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (P : Finset α) (hP : P.card ≤ r) :
    ∃ i : Fin (r + 1), ∀ x ∈ P, x ∉ E i := by
  classical
  by_contra h
  push_neg at h
  choose f hfP hfE using h
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hmem : f i ∈ E i ∩ E j := ⟨hfE i, hij ▸ hfE j⟩
    exact (Set.disjoint_left.mp (hdisj hne)) hmem.1 hmem.2
  have himg : (Finset.univ.image f).card = r + 1 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hle : (Finset.univ.image f).card ≤ P.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hfP i
  omega

/-! ### Compactness: the uniform positive minimum delta_0 of section 7.3 -/

/-- The extreme value theorem form used for delta_0: a continuous strictly
positive function on a nonempty compact space has a positive minimum. -/
theorem exists_pos_min_of_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] {f : X → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x, δ₀ ≤ f x := by
  obtain ⟨x₀, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty) hf.continuousOn
  exact ⟨f x₀, hpos x₀, fun x => hmin (Set.mem_univ x)⟩

/-- Route 7.3: on the compact space of local tuples with r + 1 continuous
boundary-distance functions delta_i, if at every point some boundary is avoided
(i.e. delta_i > 0 for some i, supplied by exists_boundary_avoiding) then the
maximum distance is uniformly bounded below by a fixed delta_0 > 0. -/
theorem uniform_positive_away {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] {r : ℕ} (δ : Fin (r + 1) → X → ℝ)
    (hcont : ∀ i, Continuous (δ i))
    (hcover : ∀ x, ∃ i, 0 < δ i x) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x, ∃ i, δ₀ ≤ δ i x := by
  classical
  haveI : Nonempty (Fin (r + 1)) := ⟨0⟩
  let g : X → ℝ := fun x =>
    (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
      (fun i => δ i x)
  have hgcont : Continuous g :=
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => hcont i)
  have hgpos : ∀ x, 0 < g x := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact lt_of_lt_of_le hi (Finset.le_sup' (fun i => δ i x) (Finset.mem_univ i))
  obtain ⟨x₀, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty) hgcont.continuousOn
  refine ⟨g x₀, hgpos x₀, fun x => ?_⟩
  have hle : g x₀ ≤ g x := hmin (Set.mem_univ x)
  have hle' : g x₀ ≤ (Finset.univ : Finset (Fin (r + 1))).sup'
      Finset.univ_nonempty (fun i => δ i x) := hle
  rw [Finset.le_sup'_iff] at hle'
  obtain ⟨i, -, hi⟩ := hle'
  exact ⟨i, hi⟩

/-! ### The universal local fields L_p of section 7.2 -/

/-- Section 7.2: L is a finite extension of Q_p (via an algebra structure)
containing an isomorphic copy of every extension of Q_p of degree at most d. -/
def ContainsBoundedExtensions (p : ℕ) [Fact p.Prime] (d : ℕ) (L : Type 0) [Field L]
    [Algebra (Padic p) L] : Prop :=
  ∀ (M : Type 0) [Field M] [Algebra (Padic p) M] [FiniteDimensional (Padic p) M],
    Module.finrank (Padic p) M ≤ d →
      ∃ f : M →ₐ[Padic p] L, Function.Injective f

/-- Section 7.2, the actual quantifier form: for every prime p and every degree
bound d there exists a finite normal extension L_p / Q_p containing an
isomorphic copy of every extension of Q_p of degree at most d.

This is the statement whose inhabitant is produced by the 7.2 construction
(finite unramified subextensions, Eisenstein polynomials, different bounds and
Krasner's lemma).  It is recorded as an explicit interface: the construction is
not yet formalized, so no inhabitant is provided here. -/
def UniversalLocalFieldExists (p : ℕ) [Fact p.Prime] (d : ℕ) : Prop :=
  ∃ (L : Type 0) (_ : Field L) (_ : Algebra (Padic p) L)
    (_ : FiniteDimensional (Padic p) L) (_ : Normal (Padic p) L),
    ContainsBoundedExtensions p d L

/-! ### The fixed G-K data of route section 7 -/

/-- The fixed G-K data: degree bound d, finite set V of primes (containing
infinity and 2 in applications), the actual disjoint family of r + 1 maps with
r = d * |V|, the uniform positive minimum delta_0, and the actual compact local
domain K_V with radius delta_0.  All of these are fixed before the point y is
given, as emphasised in route section 7.3. -/
structure GKData (n : ℕ) where
  d : ℕ
  V : Finset ℕ
  family : GluedBelyiFamily n
  r_eq : family.r = d * V.card
  delta0 : ℝ
  delta0_pos : 0 < delta0
  localDomain : KvData
  localDomain_V : localDomain.V = V
  localDomain_delta : localDomain.δ = delta0

/-- The actual analytic input of route section 7.3: the compact space X of
local tuples (one point per place in V, at most r points per tuple), the
continuous boundary-distance functions delta_i : X -> R, and the fact that
every point of X is missed by some boundary (which follows from E1: a tuple has
at most r points, so at least one of the r+1 boundaries avoids them).

INTERFACE, NO INHABITANT YET: the concrete X = product over v in V of
Y_n(L_v)^d, with delta_i built from the actual morphisms phi_i and the local
distances to {0,1,∞}, is the remaining analytic construction of section 7.3. -/
structure GKCompactInput (n r : ℕ) where
  X : Type
  top : TopologicalSpace X
  comp : CompactSpace X
  non : Nonempty X
  delta : Fin (r + 1) → X → ℝ
  delta_cont : ∀ i, Continuous (delta i)
  delta_cover : ∀ x, ∃ i, 0 < delta i x

/-- Route section 7.3: compactness produces the fixed positive minimum delta_0
of the maximum boundary distance. -/
theorem GKCompactInput.exists_delta0 {n r : ℕ} (I : GKCompactInput n r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x, ∃ i, δ₀ ≤ I.delta i x := by
  letI := I.top
  haveI := I.comp
  haveI := I.non
  exact uniform_positive_away I.delta I.delta_cont I.delta_cover

/-- Route section 7.3 assembly: the fixed G-K data (family, delta_0, local
domain) built from the compact tuple-space input.  The quantifier order is
respected: d, V, the family, delta_0 and K_V are all fixed here, before the
point y is given. -/
def GKData.ofCompactInput {n : ℕ} (d : ℕ) (V : Finset ℕ)
    (F : GluedBelyiFamily n) (r_eq : F.r = d * V.card)
    (I : GKCompactInput n F.r) (D : KvData) (DV : D.V = V)
    (hδ : D.δ = I.exists_delta0.choose) : GKData n where
  d := d
  V := V
  family := F
  r_eq := r_eq
  delta0 := I.exists_delta0.choose
  delta0_pos := I.exists_delta0.choose_spec.1
  localDomain := D
  localDomain_V := DV
  localDomain_delta := hδ

/-- The actual G-K consequence used downstream: for any finitely many points of
Y_n of cardinality at most r, some member of the fixed family has boundary
avoiding all of them. -/
theorem gk_boundary_avoids_points {n : ℕ} (G : GKData n)
    (P : Finset (fermatCurveScheme n)) (hP : P.card ≤ G.family.r) :
    ∃ i : Fin (G.family.r + 1),
      ∀ x ∈ P, x ∉ gluedBoundaryPreimage n (G.family.phi i) :=
  exists_boundary_avoiding G.family.disjoint_edges P hP

/-- The local domain of the G-K data avoids the three boundary points at every
infinite place (the actual local content of K_V). -/
theorem gk_localDomain_avoids {n : ℕ} (G : GKData n) {K : Type*} [Field K]
    [NumberField K] {lam : K} (h : InKv G.localDomain lam) :
    lam ≠ 0 ∧ lam ≠ 1 :=
  ⟨h.ne_zero, h.ne_one⟩

/-! ### Route section 7.1 recursion on the glued projective line -/

/-- One step of the section 7.1 recursion: an actual morphism to the glued
projective line together with a finite boundary witness and its specification. -/
structure P1MapStep (n : ℕ) where
  /-- The actual map phi : Y_n -> P1 (glued model). -/
  phi : fermatCurveScheme n ⟶ projectiveLineGlued
  /-- A finite witness for the boundary preimage phi^{-1}({0,1,infinity}). -/
  bd : Finset (fermatCurveScheme n)
  bd_spec : ∀ x, x ∈ bd ↔ x ∈ gluedBoundaryPreimage n phi

/-- The B1 producer input of the section 7.1 recursion: for every finite set of
points T of Y_n there is an actual morphism to the glued projective line whose
finite boundary witness avoids T.

INTERFACE, NO INHABITANT: supplied by the G-C lane from the B1 construction with
protected set S = empty.  The finite boundary witness is part of the output so
that the recursion can take T to be the union of the previous witnesses. -/
def B1StepProducer (n : ℕ) : Prop :=
  ∀ T : Finset (fermatCurveScheme n),
    ∃ step : P1MapStep n, ∀ x ∈ T, x ∉ step.bd

/-- The B1 producer in the Set.Finite form agreed with the G-C lane: for
every finite set of points T of Y_n there is an actual morphism to the glued
projective line whose boundary preimage is finite and avoids T.

INTERFACE, NO INHABITANT: this is the exact shape the stepxi (G-C) lane will
provide from the B1 construction (sigma finite fibers give the finiteness). -/
def B1FiniteProducer (n : ℕ) : Prop :=
  ∀ T : Finset (fermatCurveScheme n),
    ∃ φ : fermatCurveScheme n ⟶ projectiveLineGlued,
      (gluedBoundaryPreimage n φ).Finite ∧ (∀ x ∈ T, x ∉ gluedBoundaryPreimage n φ)

/-- Adapter: the Set.Finite form of the B1 producer gives the Finset-witness
form used by the section 7.1 recursion. -/
theorem b1StepProducer_of_finite {n : ℕ} (h : B1FiniteProducer n) :
    B1StepProducer n := by
  intro T
  obtain ⟨φ, hfin, havoid⟩ := h T
  refine ⟨⟨φ, hfin.toFinset, ?_⟩, ?_⟩
  · intro x
    exact hfin.mem_toFinset
  · intro x hx hmem
    exact havoid x hx (hfin.mem_toFinset.mp hmem)

/-- A chain of steps whose finite boundary witnesses are pairwise disjoint. -/
def GoodChain (n : ℕ) (r : ℕ)
    (phi : Fin r → (fermatCurveScheme n ⟶ projectiveLineGlued))
    (bd : Fin r → Finset (fermatCurveScheme n)) : Prop :=
  (∀ i x, x ∈ bd i ↔ x ∈ gluedBoundaryPreimage n (phi i)) ∧
  (∀ i j, i ≠ j → Disjoint (bd i) (bd j))

/-- Route section 7.1 recursion: from the B1 step producer one obtains, for
every r, r actual maps with pairwise disjoint boundary witnesses.  The new map
at each step avoids the union of the previous witnesses, hence the disjointness
of the boundaries follows from the B1 avoid condition. -/
theorem exists_goodChain (n : ℕ) (hb1 : B1StepProducer n) :
    ∀ r : ℕ, ∃ phi bd, GoodChain n r phi bd := by
  classical
  intro r
  induction r with
  | zero =>
      refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ m ih =>
      obtain ⟨phi, bd, hspec, hdisj⟩ := ih
      set T : Finset (fermatCurveScheme n) :=
        (Finset.univ : Finset (Fin m)).biUnion bd with hT
      have hmemT : ∀ (i : Fin m) {x}, x ∈ bd i → x ∈ T := by
        intro i x hx
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
      obtain ⟨step, hstep⟩ := hb1 T
      refine ⟨Fin.snoc (α := fun _ => fermatCurveScheme n ⟶ projectiveLineGlued)
          phi step.phi,
        Fin.snoc (α := fun _ => Finset (fermatCurveScheme n)) bd step.bd, ?_, ?_⟩
      · intro i x
        cases i using Fin.lastCases with
        | last =>
            rw [Fin.snoc_last, Fin.snoc_last]
            exact step.bd_spec x
        | cast j =>
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hspec j x
      · intro i j hij
        cases i using Fin.lastCases with
        | last =>
            cases j using Fin.lastCases with
            | last => exact absurd rfl hij
            | cast j' =>
                refine Finset.disjoint_left.mpr (fun x hxlast hxold => ?_)
                rw [Fin.snoc_last] at hxlast
                rw [Fin.snoc_castSucc] at hxold
                exact hstep x (hmemT j' hxold) hxlast
        | cast i' =>
            cases j using Fin.lastCases with
            | last =>
                refine Finset.disjoint_left.mpr (fun x hxold hxlast => ?_)
                rw [Fin.snoc_castSucc] at hxold
                rw [Fin.snoc_last] at hxlast
                exact hstep x (hmemT i' hxold) hxlast
            | cast j' =>
                rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
                exact hdisj i' j' (fun h => hij (by rw [h]))

/-- Existence of the G-K finite family of route section 7.1 on the glued
projective line, with r = d * |V|, from the B1 step producer. -/
theorem hasGluedBelyiFamily_of_b1 (n d : ℕ) (V : Finset ℕ)
    (hb1 : B1StepProducer n) : HasGluedBelyiFamily n d V := by
  classical
  obtain ⟨phi, bd, hspec, hdisj⟩ := exists_goodChain n hb1 (d * V.card + 1)
  refine ⟨⟨d * V.card, phi, ?_⟩, rfl⟩
  intro i j hij
  refine Set.disjoint_left.mpr (fun x hxi hxj => ?_)
  exact Finset.disjoint_left.mp (hdisj i j hij) ((hspec i x).mpr hxi) ((hspec j x).mpr hxj)

#print axioms b1StepProducer_of_finite
#print axioms exists_goodChain
#print axioms hasGluedBelyiFamily_of_b1

#print axioms exists_boundary_avoiding
#print axioms exists_pos_min_of_compact
#print axioms uniform_positive_away
#print axioms gk_boundary_avoids_points

end LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
end
