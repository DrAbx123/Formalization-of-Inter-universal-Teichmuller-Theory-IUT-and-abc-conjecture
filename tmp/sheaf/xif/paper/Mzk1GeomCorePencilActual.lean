import Mathlib
import tmp.external.ported.flt_test.Definitions.Def_AlgebraicCurve_RiemannRochRows
import tmp.sheaf.xif.paper.Mzk1GeometricCorePreciseActual

/-!
# Problem D — GeometricCore from the function field (pencil `g = 1 / h`)

Source: `coord/ProblemD_GeometricCoreSkeleton.lean` (skeleton, never compiled),
`coord/OPEN-HARD-PROBLEMS.md` Problem D, paper lines 222-265.

What the rest of the proof of Theorem 2.5 consumes from `psi : X -> P^1` is only
"`psi^{-1}(0) = T` with all multiplicities one", i.e. a function `g` whose zero divisor is
exactly `sum_{t in T} t`.  The isomorphism `psi^* O(1) = O(D)` is how the paper builds
`psi`; it is not used afterwards.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual

universe u



theorem ell_drop_of_rr {g ellD ellDt ellKD ellKDt degD : ℤ}
    (h1 : ellD - ellKD = degD + 1 - g)
    (h2 : ellDt - ellKDt = (degD - 1) + 1 - g)
    (v1 : ellKD = 0) (v2 : ellKDt = 0) : ellD - ellDt = 1 := by
  omega

theorem exists_mem_notMem_of_proper {K V ι : Type*} [Field K] [Infinite K]
    [AddCommGroup V] [Module K V] (s : Finset ι) (W : ι → Submodule K V)
    (U : Submodule K V) (h : ∀ i ∈ s, W i < U) :
    ∃ v ∈ U, ∀ i ∈ s, v ∉ W i := by
  classical
  set W' : ι → Submodule K U := fun i => Submodule.comap U.subtype (W i) with hW'
  have htop : (⊤ : Submodule K U) ∉ s.image W' := by
    intro hmem
    obtain ⟨i, hi, hWi⟩ := Finset.mem_image.mp hmem
    have hle : U ≤ W i := Submodule.comap_subtype_eq_top.mp hWi
    exact (not_le_of_gt (h i hi)) hle
  have hne : (⋃ p ∈ s.image W', (p : Set U)) ≠ Set.univ :=
    Subspace.biUnion_ne_univ_of_top_notMem htop
  obtain ⟨v, hv⟩ : ∃ v : U, v ∉ ⋃ p ∈ s.image W', (p : Set U) := by
    by_contra hc
    push Not at hc
    exact hne (Set.eq_univ_of_forall hc)
  refine ⟨(v : V), v.2, fun i hi hvi => ?_⟩
  have hmemW : v ∈ W' i := by
    rw [hW', Submodule.mem_comap]
    exact hvi
  exact hv (Set.mem_biUnion (Finset.mem_image_of_mem W' hi) hmemW)

structure PencilData (K F P : Type*) [Field K] [Field F] [Algebra K F] where
  ord : P → F → ℤ
  T : Finset P
  LD : Submodule K F
  LDt : P → Submodule K F
  proper : ∀ t ∈ T, LDt t < LD
  pole : ∀ h ∈ LD, ∀ t ∈ T, h ∉ LDt t → ord t h = -1
  regular : ∀ h ∈ LD, h ≠ 0 → ∀ p, p ∉ T → 0 ≤ ord p h
  ord_inv : ∀ p (h : F), h ≠ 0 → ord p h⁻¹ = -ord p h

theorem exists_simple_pole_function {K F P : Type*} [Field K] [Infinite K] [Field F]
    [Algebra K F] (X : PencilData K F P) (hT : X.T.Nonempty) :
    ∃ h ∈ X.LD, h ≠ 0 ∧ (∀ t ∈ X.T, X.ord t h = -1) ∧
      ∀ p, p ∉ X.T → 0 ≤ X.ord p h := by
  obtain ⟨v, hvU, hvW⟩ := exists_mem_notMem_of_proper X.T X.LDt X.LD X.proper
  have hv0 : v ≠ 0 := by
    obtain ⟨t, ht⟩ := hT
    intro h0
    exact hvW t ht (by rw [h0]; exact (X.LDt t).zero_mem)
  exact ⟨v, hvU, hv0, fun t ht => X.pole v hvU t ht (hvW t ht),
    fun p hp => X.regular v hvU hv0 p hp⟩

theorem exists_function_with_zero_divisor {K F P : Type*} [Field K] [Infinite K]
    [Field F] [Algebra K F] (X : PencilData K F P) (hT : X.T.Nonempty) :
    ∃ g : F, g ≠ 0 ∧ (∀ t ∈ X.T, X.ord t g = 1) ∧
      ∀ p, p ∉ X.T → X.ord p g ≤ 0 := by
  obtain ⟨h, hhLD, hh0, hpole, hreg⟩ := exists_simple_pole_function X hT
  refine ⟨h⁻¹, inv_ne_zero hh0, fun t ht => ?_, fun p hp => ?_⟩
  · rw [X.ord_inv t h hh0, hpole t ht]
    norm_num
  · rw [X.ord_inv p h hh0]
    linarith [hreg p hp]

def zeroSet {K F P : Type*} [Field K] [Field F] [Algebra K F]
    (X : PencilData K F P) (g : F) : Set P := {p | 0 < X.ord p g}

structure GeometricCoreZeroDatum (K F P : Type*) [Field K] [Field F] [Algebra K F]
    (X : PencilData K F P) where
  g : F
  g_ne_zero : g ≠ 0
  zero_simple : ∀ t ∈ X.T, X.ord t g = 1
  no_other_zero : ∀ p, p ∉ X.T → X.ord p g ≤ 0

theorem exists_geometricCore_zeroDatum {K F P : Type*} [Field K] [Infinite K] [Field F]
    [Algebra K F] (X : PencilData K F P) (hT : X.T.Nonempty) :
    Nonempty (GeometricCoreZeroDatum K F P X) := by
  obtain ⟨g, hg0, hz, hn⟩ := exists_function_with_zero_divisor X hT
  exact ⟨{ g := g, g_ne_zero := hg0, zero_simple := hz, no_other_zero := hn }⟩

theorem zeroSet_eq_T {K F P : Type*} [Field K] [Field F] [Algebra K F]
    (X : PencilData K F P) (D : GeometricCoreZeroDatum K F P X) :
    zeroSet X D.g = ↑X.T := by
  ext p
  constructor
  · intro hp
    by_contra hpT
    exact absurd hp (not_lt.mpr (D.no_other_zero p hpT))
  · intro hp
    rw [Finset.mem_coe] at hp
    show 0 < X.ord p D.g
    rw [D.zero_simple p hp]
    norm_num

theorem zero_divisor_eq_one {K F P : Type*} [Field K] [Field F] [Algebra K F]
    (X : PencilData K F P) (D : GeometricCoreZeroDatum K F P X) {p : P} (hp : p ∈ X.T) :
    max (X.ord p D.g) 0 = 1 := by
  rw [D.zero_simple p hp]
  norm_num

theorem zero_divisor_eq_zero {K F P : Type*} [Field K] [Field F] [Algebra K F]
    (X : PencilData K F P) (D : GeometricCoreZeroDatum K F P X) {p : P} (hp : p ∉ X.T) :
    max (X.ord p D.g) 0 = 0 :=
  max_eq_right (D.no_other_zero p hp)

theorem zero_divisor_degree {K F P : Type*} [Field K] [Field F] [Algebra K F]
    (X : PencilData K F P) (D : GeometricCoreZeroDatum K F P X) :
    (∑ t ∈ X.T, X.ord t D.g) = (X.T.card : ℤ) := by
  have h : (∑ t ∈ X.T, X.ord t D.g) = ∑ t ∈ X.T, (1 : ℤ) :=
    Finset.sum_congr rfl fun t ht => D.zero_simple t ht
  rw [h]
  simp


/-! ## 4. The restated precise witness on the ported function-field API

The ported Riemann-Roch statement is `AlgebraicCurve.FunctionFieldRiemannRoch`
(`tmp/external/ported/flt_test/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean:47`):
`l(D) - l(K - D) = deg D + 1 - g` for every divisor `D`.  Here `L(D) = LSpace D` is a
`K`-subspace of the function field `F` and `l(D) = ell D = finrank_K L(D)`.

Hypotheses of the restated witness, in the paper language:
* `[IsAlgClosed K]`: the base field is algebraically closed;
* `[IsCurveOver K F]`: `F` is the function field of a smooth proper connected curve over
  `K` in the ported interface (finite residue field extensions + rank-one Kaehler module);
* `[HasCanonicalDivisor (K := K) (F := F)]` and `[∀ v, v.DCoordGenerates]`: canonical
  divisors and local residue coordinates, as required by the ported Riemann-Roch rows;
* `T : Finset (Place K F)`: `T` is finite;
* `2 * genus K F + 1 <= T.card`: the numerical hypothesis `deg D >= 2g + 1`. -/

namespace Curve

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def punctureDivisor (T : Finset (Place K F)) : Divisor K F :=
  ∑ t ∈ T, Finsupp.single t (1 : ℤ)

theorem punctureDivisor_apply_of_mem {T : Finset (Place K F)} {v : Place K F}
    (hv : v ∈ T) : punctureDivisor T v = 1 := by
  classical
  have h : ∀ t ∈ T, Finsupp.single t (1 : ℤ) v = (if t = v then (1 : ℤ) else 0) := by
    intro t _
    rw [Finsupp.single_apply]
  rw [punctureDivisor, Finset.sum_apply', Finset.sum_congr rfl h,
    Finset.sum_ite_eq' T v (fun _ => (1 : ℤ)), if_pos hv]

theorem punctureDivisor_apply_of_notMem {T : Finset (Place K F)} {v : Place K F}
    (hv : v ∉ T) : punctureDivisor T v = 0 := by
  classical
  have h : ∀ t ∈ T, Finsupp.single t (1 : ℤ) v = (if t = v then (1 : ℤ) else 0) := by
    intro t _
    rw [Finsupp.single_apply]
  rw [punctureDivisor, Finset.sum_apply', Finset.sum_congr rfl h,
    Finset.sum_ite_eq' T v (fun _ => (1 : ℤ)), if_neg hv]

theorem punctureDivisor_sub_single_le (T : Finset (Place K F)) (t : Place K F) :
    punctureDivisor T - Finsupp.single t (1 : ℤ) ≤ punctureDivisor T := by
  classical
  rw [Finsupp.le_def]
  intro v
  rw [Finsupp.sub_apply]
  have hs : (0 : ℤ) ≤ Finsupp.single t (1 : ℤ) v := by
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  linarith

/-- §deg D = |T|§: over an algebraically closed base every place has degree one, so the
divisor of the prescribed points has degree the cardinality of §T§. -/
theorem degree_punctureDivisor {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (punctureDivisor T) = (T.card : ℤ) := by
  classical
  rw [punctureDivisor, map_sum]
  have h : ∀ t ∈ T, Divisor.degree (Finsupp.single t (1 : ℤ)) = 1 := by
    intro t _
    rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed t]
    norm_num
  rw [Finset.sum_congr rfl h]
  simp

structure GeomCorePencilWitness (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (T : Finset (Place K F)) where
  g : F
  g_ne_zero : g ≠ 0
  zero_simple : ∀ t ∈ T, t.ord g = 1
  no_other_zero : ∀ p : Place K F, p ∉ T → p.ord g ≤ 0

def GeomCorePencilRecast (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (T : Finset (Place K F)) : Prop :=
  Nonempty (GeomCorePencilWitness K F T)

theorem GeomCorePencilWitness.zero_locus_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    {T : Finset (Place K F)} (W : GeomCorePencilWitness K F T) :
    {p : Place K F | 0 < p.ord W.g} = ↑T := by
  ext p
  constructor
  · intro hp
    by_contra hpT
    exact absurd hp (not_lt.mpr (W.no_other_zero p hpT))
  · intro hp
    rw [Finset.mem_coe] at hp
    show 0 < p.ord W.g
    rw [W.zero_simple p hp]
    norm_num

/- The three geometric facts that Theorem 2.5 consumes from the map `psi` to
`P^1`: the fibre over `0` is `T`, every point of the fibre is unramified (multiplicity
one), and the complement of `T` does not meet the fibre over `0`. -/
theorem GeomCorePencilWitness.unramified_over_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    {T : Finset (Place K F)} (W : GeomCorePencilWitness K F T) :
    {p : Place K F | 0 < p.ord W.g} = ↑T ∧ (∀ t ∈ T, t.ord W.g = 1) ∧
      (∀ p : Place K F, p ∉ T → ¬ 0 < p.ord W.g) :=
  ⟨W.zero_locus_eq, W.zero_simple, fun p hp => not_lt.mpr (W.no_other_zero p hp)⟩

theorem GeomCorePencilWitness.zero_locus_degree {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    {T : Finset (Place K F)} (W : GeomCorePencilWitness K F T) :
    (∑ t ∈ T, t.ord W.g) = (T.card : ℤ) := by
  have h : (∑ t ∈ T, t.ord W.g) = ∑ t ∈ T, (1 : ℤ) :=
    Finset.sum_congr rfl fun t ht => W.zero_simple t ht
  rw [h]
  simp


/-- **Conditional construction of the restated precise witness.**

Inputs:
* `hRR`: the ported Riemann-Roch statement `AlgebraicCurve.FunctionFieldRiemannRoch K F`;
* `hdual`: vanishing of `l(K - D)` and `l(K - (D - t))`.  For `D = sum T` with
  `|T| >= 2g + 1` these follow from `deg (K - D) = 2g - 2 - |T| < 0` together with
  `l(E) = 0` for `deg E < 0`.  Two ported pieces are missing for that derivation:
  (a) `deg (canonicalDivisorOf omega) = 2g - 2`: the ported `genus` is *defined* as
  `(deg K + 2) / 2` and no lemma recovers the degree from it; (b) `l(E) = 0` for
  `deg E < 0`: `AlgebraicCurve.ell_eq_zero_of_degree_neg` is ported only in the
  `flt_th` tree, which is not import-compatible with the `flt_test` tree that carries
  `FunctionFieldRiemannRoch` (both declare `AlgebraicCurve.Divisor.degree`; importing
  both fails with "environment already contains ...").  Hence `hdual` is an explicit
  named input here, not derived from `hcard`;
* `hcard`: the paper numerical hypothesis `|T| >= 2g + 1`; it is used only to derive
  `T.Nonempty`, and it is what makes `hdual` true.

The proof takes `h in L(D)` outside every `L(D - t)` (sections 1-3) and returns
`g = h^{-1}`, whose zero divisor is `sum T` with all multiplicities one. -/
theorem exists_geometricCore_of_riemannRoch {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates]
    {ω : KaehlerDifferential K F} (hω : ω ≠ 0)
    (T : Finset (Place K F)) (hcard : 2 * genus K F + 1 ≤ T.card)
    (hdual : ∀ t ∈ T,
      (ell (canonicalDivisorOf hω - punctureDivisor T) : ℤ) = 0 ∧
      (ell (canonicalDivisorOf hω - (punctureDivisor T - Finsupp.single t (1 : ℤ))) : ℤ) = 0)
    (hRR : FunctionFieldRiemannRoch K F) :
    Nonempty (GeomCorePencilWitness K F T) := by
  classical
  -- the paper hypothesis `|T| >= 2g + 1` in particular makes `T` nonempty
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  have hproper : ∀ t ∈ T,
      LSpace (punctureDivisor T - Finsupp.single t (1 : ℤ)) < LSpace (punctureDivisor T) := by
    intro t ht
    refine lt_of_le_of_ne (lSpace_mono (punctureDivisor_sub_single_le T t)) ?_
    intro heq
    have h1 : (ell (punctureDivisor T) : ℤ)
        - (ell (canonicalDivisorOf hω - punctureDivisor T) : ℤ)
        = (Divisor.degree (punctureDivisor T) : ℤ) + 1 - (genus K F : ℤ) :=
      hRR hω (punctureDivisor T)
    have h2 : (ell (punctureDivisor T - Finsupp.single t (1 : ℤ)) : ℤ)
        - (ell (canonicalDivisorOf hω
            - (punctureDivisor T - Finsupp.single t (1 : ℤ))) : ℤ)
        = ((Divisor.degree (punctureDivisor T) : ℤ) - 1) + 1 - (genus K F : ℤ) := by
      have h := hRR hω (punctureDivisor T - Finsupp.single t (1 : ℤ))
      have hdeg : (Divisor.degree (punctureDivisor T - Finsupp.single t (1 : ℤ)) : ℤ)
          = (Divisor.degree (punctureDivisor T) : ℤ) - 1 := by
        rw [map_sub, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed t]
        norm_num
      rw [hdeg] at h
      linarith [h]
    have hdrop := ell_drop_of_rr h1 h2 (hdual t ht).1 (hdual t ht).2
    have heq' : (ell (punctureDivisor T - Finsupp.single t (1 : ℤ)) : ℤ)
        = (ell (punctureDivisor T) : ℤ) :=
      congrArg (fun s : Submodule K F => (Module.finrank K s : ℤ)) heq
    linarith
  let X : PencilData K F (Place K F) :=
    { ord := fun (p : Place K F) (f : F) => p.ord f
      T := T
      LD := LSpace (punctureDivisor T)
      LDt := fun t => LSpace (punctureDivisor T - Finsupp.single t (1 : ℤ))
      proper := hproper
      pole := by
        intro h hh t ht hmem
        have hnot : ¬ (h = 0 ∨ ∀ v : Place K F,
            -(punctureDivisor T - Finsupp.single t (1 : ℤ)) v ≤ v.ord h) := by
          simpa only [mem_lSpace_iff_ord] using hmem
        obtain ⟨hh0, hnotall⟩ := not_or.mp hnot
        obtain ⟨v, hv⟩ := not_forall.mp hnotall
        rw [not_le] at hv
        have hreg : ∀ w : Place K F, -punctureDivisor T w ≤ w.ord h :=
          (mem_lSpace_iff_ord.mp hh).resolve_left hh0
        by_cases hvt : v = t
        · rw [hvt] at hv
          have hDt : punctureDivisor T t = 1 := punctureDivisor_apply_of_mem ht
          have hval : (punctureDivisor T - Finsupp.single t (1 : ℤ)) t = 0 := by
            rw [Finsupp.sub_apply, hDt, Finsupp.single_eq_same]
            norm_num
          rw [hval, neg_zero] at hv
          have hge : -1 ≤ t.ord h := by
            have := hreg t
            rwa [hDt] at this
          omega
        · exfalso
          have hsingle : Finsupp.single t (1 : ℤ) v = 0 := by
            rw [Finsupp.single_apply, if_neg (Ne.symm hvt)]
          have hval : (punctureDivisor T - Finsupp.single t (1 : ℤ)) v
              = punctureDivisor T v := by
            rw [Finsupp.sub_apply, hsingle, sub_zero]
          rw [hval] at hv
          exact absurd hv (not_lt.mpr (hreg v))
      regular := by
        intro h hh hh0 p hp
        have hreg := (mem_lSpace_iff_ord.mp hh).resolve_left hh0
        have hDp : punctureDivisor T p = 0 := punctureDivisor_apply_of_notMem hp
        simpa [hDp] using hreg p
      ord_inv := by
        intro p f _
        exact Place.ord_inv p f }
  obtain ⟨D⟩ := exists_geometricCore_zeroDatum X hT
  exact Nonempty.intro ⟨D.g, D.g_ne_zero, D.zero_simple, D.no_other_zero⟩


/-- Row record: what is proved, what is conditional and what is missing (Problem D). -/
def geomCorePencilRows : List (String × String × String) :=
  [ ("ell_drop_of_rr (Riemann-Roch arithmetic)", "PROVED",
      "omega from the two Riemann-Roch instances"),
    ("exists_mem_notMem_of_proper", "PROVED",
      "Mathlib Subspace.biUnion_ne_univ_of_top_notMem inside U"),
    ("exists_simple_pole_function", "PROVED",
      "choice outside all L(D - t); nonzero because outside L(D - t) for t in T"),
    ("exists_function_with_zero_divisor (g = 1/h)", "PROVED",
      "ord_inv: simple zeros on T, no other zeros"),
    ("GeometricCore function-field form", "PROVED",
      "zero locus = T, pointwise zero divisor = sum T, deg = |T|"),
    ("restated precise witness", "DEFINED",
      "IsAlgClosed K, IsCurveOver K F, HasCanonicalDivisor, T finite, 2g+1 <= |T|"),
    ("conditional construction from ported FunctionFieldRiemannRoch", "PROVED CONDITIONAL",
      "inputs: hRR and dual vanishing; deg < 0 implies ell = 0 is not in the ported API"),
    ("MapsTToZero vacuity", "FIXED",
      "MapsTToZeroOn requires T subset U; old condition is vacuous when T misses U"),
    ("line bundle iso psi^* O(1) = O(D)", "NAMED class-B input",
      "not addressed here; not used by Theorem 2.5 after psi is built") ]

theorem geomCorePencilRows_length : geomCorePencilRows.length = 9 := rfl

end Curve

section SchemeLevel

open CategoryTheory AlgebraicGeometry NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual

/-- Restated `maps_T_to_zero`: `T` lies in the open `U` where the finite map is described,
and the map vanishes on `T` (non-vacuous form of the paper condition on psi). -/
def MapsTToZeroOn {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (fm : Mzk1FiniteMapData c ε) (T : Set C) : Prop :=
  T ⊆ (fm.U : Set C) ∧ ∀ t ∈ T, t ∉ (C.basicOpen fm.f : Set C)

theorem mapsTToZero_of_on {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {fm : Mzk1FiniteMapData c ε} {T : Set C} (h : MapsTToZeroOn c ε fm T) :
    MapsTToZero c ε fm T :=
  fun t ht _ => h.2 t ht

theorem mapsTToZero_of_disjoint {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (fm : Mzk1FiniteMapData c ε) {T : Set C} (h : Disjoint T (fm.U : Set C)) :
    MapsTToZero c ε fm T := by
  intro t ht hU _
  exact (Set.disjoint_left.mp h) ht hU

theorem mapsTToZeroOn_iff {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (fm : Mzk1FiniteMapData c ε) (T : Set C) :
    MapsTToZeroOn c ε fm T ↔ T ⊆ (fm.U : Set C) ∧ MapsTToZero c ε fm T := by
  constructor
  · intro h
    exact ⟨h.1, fun t ht _ => h.2 t ht⟩
  · rintro ⟨hTU, h⟩
    exact ⟨hTU, fun t ht => h t ht (hTU ht)⟩

end SchemeLevel

end LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual
