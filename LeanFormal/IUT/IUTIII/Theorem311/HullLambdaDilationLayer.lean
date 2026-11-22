/-
# G1 statement layer: the hull as the least `lambda . O` dilation (reduced spec)

Probe file (run `hull-presentation-routes-20261016`, agent Noether), read-only with
respect to every other file; it adds declarations only.  Statement layer for the G1
reading of the holomorphic hull, kept in reduced form (the coordination log carries
the full passage):

* Source, reduced (via `logs/coordination/wild-brainstorm-20261017.md` section G1,
  quoting IUT III, Remark 3.9.5, (i), corpus lines 7794-7811): the holomorphic hull
  of a region is "the smallest subset of the form ... lambda . O ..." whose "each
  component of lambda ... is nonzero" that contains the region; if the region is "not
  relatively compact", the hull is defined "to be" the whole ambient.
* Consumers: the `lambda . O` slot consumers `scaledRegionImage`
  (`SourceImageHull.lean:277`), `SourceUnitRegionHaarData.hull_subset_scaledRegionImage`
  (`IQCarrierHaarData.lean:168`), and `IQHullLogVolumeInterface.unitRegion` /
  `scaleShift` / `hull_subset_scaleShift` (`SourceHullCompactnessReduction.lean:52`);
  boundary table R1-R5 in `logs/coordination/hull-presentation-routes-20261016.md`.
* The existing occupant of the name (not of this content): `IsLambdaOHull`
  (`SourceImageHull.lean:513`) records the hull form only, with no leastness, no
  componentwise-nonzero content and no dichotomy; the names below are distinct and
  that file is not touched.

Three-state: every theorem below is proved about the toy model (componentwise
dilations of the symmetric unit cube in `iota -> Real`, coefficients in
`WithTop Real`).  Fidelity of the toy to the source G1 reading is candidate /
needs-verification: "componentwise nonzero" is modelled by nonzero coefficients,
"relatively compact" by finite coefficients, and the `I^Q` branch by the all-`top`
family.  No claim about the original text or the arithmetic carrier is made.
-/

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT

namespace HullLambdaDilation

variable {ι : Type*}

/-- Componentwise dilation of the symmetric unit cube: `x` lies in `cubeDilation lam`
if every coordinate satisfies `|x i| ≤ lam i`.  Coefficients live in `WithTop Real`:
`⊤` is the "no constraint in this component" coefficient of the unbounded (`I^Q`)
branch of the source reading. -/
def cubeDilation (lam : ι → WithTop Real) : Set (ι → Real) :=
  {x | ∀ i, ((|x i| : Real) : WithTop Real) ≤ lam i}

theorem cubeDilation_mono {lam mu : ι → WithTop Real} (h : ∀ i, lam i ≤ mu i) :
    cubeDilation lam ⊆ cubeDilation mu :=
  fun _ hx i => le_trans (hx i) (h i)

/-- The inclusion lattice of admissible dilations is the componentwise order: for
nonnegative coefficients, inclusion of the dilated regions is equivalent to
componentwise comparison of the coefficients. -/
theorem cubeDilation_le_iff {lam mu : ι → WithTop Real}
    (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ i, 0 ≤ mu i) :
    cubeDilation lam ⊆ cubeDilation mu ↔ ∀ i, lam i ≤ mu i := by
  classical
  constructor
  · intro hsub i
    by_contra hle
    have hlt : mu i < lam i := not_le.mp hle
    have hmu_ne_top : mu i ≠ ⊤ := by
      intro htop
      rw [htop] at hlt
      exact not_lt_of_ge le_top hlt
    obtain ⟨b, hb'⟩ := WithTop.ne_top_iff_exists.mp hmu_ne_top
    have hb : mu i = (b : WithTop Real) := hb'.symm
    rw [hb] at hlt
    rcases eq_or_ne (lam i) ⊤ with htop | hne
    · have hxmem : Function.update (0 : ι → Real) i (|b| + 1) ∈ cubeDilation lam := by
        intro j
        by_cases hj : j = i
        · rw [hj, Function.update_self, htop]
          exact le_top
        · rw [Function.update_of_ne hj]
          simpa using hlam j
      have hxout : Function.update (0 : ι → Real) i (|b| + 1) ∉ cubeDilation mu := by
        intro hmem
        have hcoord := hmem i
        rw [Function.update_self, hb] at hcoord
        have hle' : |(|b| + 1)| ≤ b := WithTop.coe_le_coe.mp hcoord
        rw [abs_of_nonneg (show (0 : Real) ≤ |b| + 1 by positivity)] at hle'
        exact absurd hle' (not_le.mpr (lt_of_le_of_lt (le_abs_self b) (lt_add_one (|b|))))
      exact hxout (hsub hxmem)
    · obtain ⟨a, ha'⟩ := WithTop.ne_top_iff_exists.mp hne
      have ha : lam i = (a : WithTop Real) := ha'.symm
      rw [ha] at hlt
      have hba : b < a := WithTop.coe_lt_coe.mp hlt
      have ha0 : 0 ≤ a := by
        have h0a := hlam i
        rw [ha] at h0a
        exact WithTop.coe_le_coe.mp h0a
      have hxmem : Function.update (0 : ι → Real) i a ∈ cubeDilation lam := by
        intro j
        by_cases hj : j = i
        · rw [hj, Function.update_self, ha]
          exact WithTop.coe_le_coe.mpr (le_of_eq (abs_of_nonneg ha0))
        · rw [Function.update_of_ne hj]
          simpa using hlam j
      have hxout : Function.update (0 : ι → Real) i a ∉ cubeDilation mu := by
        intro hmem
        have hcoord := hmem i
        rw [Function.update_self, hb] at hcoord
        have hle' : |a| ≤ b := WithTop.coe_le_coe.mp hcoord
        rw [abs_of_nonneg ha0] at hle'
        exact absurd hle' (not_le.mpr hba)
      exact hxout (hsub hxmem)
  · intro h x hx
    exact fun i => le_trans (hx i) (h i)

/-- The all-`⊤` coefficient family dilates the cube to the whole ambient. -/
theorem cubeDilation_top : cubeDilation (fun _ : ι => (⊤ : WithTop Real)) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _ i
    exact le_top

/-- The all-`⊤` family is the only one whose dilation is the whole ambient: mixed
finite and `⊤` coefficients give proper regions. -/
theorem cubeDilation_eq_univ_iff (lam : ι → WithTop Real) :
    cubeDilation lam = Set.univ ↔ ∀ i, lam i = ⊤ := by
  classical
  constructor
  · intro h i
    by_contra hne
    obtain ⟨a, ha'⟩ := WithTop.ne_top_iff_exists.mp hne
    have ha : lam i = (a : WithTop Real) := ha'.symm
    have hxin : Function.update (0 : ι → Real) i (|a| + 1) ∈ cubeDilation lam := by
      rw [h]
      exact Set.mem_univ _
    have hcoord : ((|(|a| + 1)| : Real) : WithTop Real) ≤ lam i := by
      simpa only [Function.update_self] using hxin i
    rw [ha] at hcoord
    have hle : |(|a| + 1)| ≤ a := WithTop.coe_le_coe.mp hcoord
    rw [abs_of_nonneg (show (0 : Real) ≤ |a| + 1 by positivity)] at hle
    exact absurd hle (not_le.mpr (lt_of_le_of_lt (le_abs_self a) (lt_add_one (|a|))))
  · intro h
    have hfun : lam = fun _ => (⊤ : WithTop Real) := funext h
    rw [hfun]
    exact cubeDilation_top

/-- Zero coefficients collapse the corresponding coordinate: the
componentwise-nonzero condition of the source reading is forced by the data. -/
theorem cubeDilation_zero_coordinate {lam : ι → WithTop Real} {i : ι} (h : lam i = 0)
    {x : ι → Real} (hx : x ∈ cubeDilation lam) : x i = 0 := by
  have h1 : ((|x i| : Real) : WithTop Real) ≤ (0 : WithTop Real) := by
    have h2 := hx i
    rwa [h] at h2
  have h3 : |x i| ≤ 0 := WithTop.coe_le_coe.mp h1
  exact abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _))

theorem not_mem_cubeDilation_of_zero_coefficient {lam : ι → WithTop Real} {i : ι}
    (h : lam i = 0) {p : ι → Real} (hp : p i ≠ 0) : p ∉ cubeDilation lam :=
  fun hmem => hp (cubeDilation_zero_coordinate h hmem)

theorem coefficient_ne_zero_of_witness {lam : ι → WithTop Real} {T : Set (ι → Real)}
    (hsub : T ⊆ cubeDilation lam) {i : ι} {p : ι → Real} (hp : p ∈ T) (hpi : p i ≠ 0) :
    lam i ≠ 0 :=
  fun h0 => not_mem_cubeDilation_of_zero_coefficient h0 hpi (hsub hp)

/-- Admissible dilation data: nonnegative coefficients.  Negative coefficients would
make `cubeDilation` empty and break the inclusion lattice, so the comparisons of
dilations below are between admissible families. -/
def IsAdmissibleDilationCoefficient (lam : ι → WithTop Real) : Prop := ∀ i, 0 ≤ lam i

/-- The coefficient form of "the smallest subset of the form `lambda . O` that
contains the data": `lam` is the componentwise least admissible upper bound of the
coordinate absolute values of `T`. -/
def IsCoordinatewiseAbsSup (T : Set (ι → Real)) (lam : ι → WithTop Real) : Prop :=
  (∀ i, ∀ x ∈ T, ((|x i| : Real) : WithTop Real) ≤ lam i) ∧
    ∀ mu : ι → WithTop Real,
      (∀ i, ∀ x ∈ T, ((|x i| : Real) : WithTop Real) ≤ mu i) → ∀ i, lam i ≤ mu i

/-- `lam` is the smallest admissible `lambda . O` data containing `T`. -/
def IsLeastCubeDilationOf (T : Set (ι → Real)) (lam : ι → WithTop Real) : Prop :=
  IsAdmissibleDilationCoefficient lam ∧ T ⊆ cubeDilation lam ∧
    ∀ mu : ι → WithTop Real, IsAdmissibleDilationCoefficient mu →
      T ⊆ cubeDilation mu → cubeDilation lam ⊆ cubeDilation mu

/-- Leastness from the componentwise sup characterization. -/
theorem isLeastCubeDilationOf_of_isCoordinatewiseAbsSup {T : Set (ι → Real)}
    {lam : ι → WithTop Real} (h : IsCoordinatewiseAbsSup T lam) (hT : T.Nonempty) :
    IsLeastCubeDilationOf T lam := by
  refine ⟨?_, fun x hx i => h.1 i x hx, ?_⟩
  · intro i
    obtain ⟨x, hx⟩ := hT
    exact le_trans (WithTop.coe_le_coe.mpr (abs_nonneg (x i))) (h.1 i x hx)
  · intro mu _ hsub
    exact cubeDilation_mono fun i => h.2 mu (fun j x hx => hsub hx j) i

theorem isLeastCubeDilationOf_coefficient_ne_zero_of_witness {T : Set (ι → Real)}
    {lam : ι → WithTop Real} (h : IsLeastCubeDilationOf T lam) {i : ι} {p : ι → Real}
    (hp : p ∈ T) (hpi : p i ≠ 0) : lam i ≠ 0 :=
  coefficient_ne_zero_of_witness h.2.1 hp hpi

/-- Box data attain their componentwise sup: the box is the least admissible dilation
of itself, the attained case of the source's least-dilation optimization. -/
theorem isCoordinatewiseAbsSup_boxDilation {r : ι → Real} (hr : ∀ i, 0 ≤ r i) :
    IsCoordinatewiseAbsSup (cubeDilation (fun i => (r i : WithTop Real)))
      (fun i => (r i : WithTop Real)) := by
  classical
  constructor
  · intro i x hx
    exact hx i
  · intro mu hmu i
    have hxmem : Function.update (0 : ι → Real) i (r i) ∈
        cubeDilation (fun j => (r j : WithTop Real)) := by
      intro j
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        exact WithTop.coe_le_coe.mpr (le_of_eq (abs_of_nonneg (hr i)))
      · rw [Function.update_of_ne hj]
        simpa using WithTop.coe_le_coe.mpr (hr j)
    have hcoord := hmu i (Function.update (0 : ι → Real) i (r i)) hxmem
    rwa [Function.update_self, abs_of_nonneg (hr i)] at hcoord

theorem isLeastCubeDilationOf_boxDilation {r : ι → Real} (hr : ∀ i, 0 ≤ r i) :
    IsLeastCubeDilationOf (cubeDilation (fun i => (r i : WithTop Real)))
      (fun i => (r i : WithTop Real)) :=
  isLeastCubeDilationOf_of_isCoordinatewiseAbsSup (isCoordinatewiseAbsSup_boxDilation hr)
    ⟨0, fun i => by simpa using WithTop.coe_le_coe.mpr (hr i)⟩

/-- Finite-coefficient dilations are boxes (finite products of closed intervals), the
toy shadow of the "relatively compact" branch of the source reading. -/
theorem cubeDilation_eq_pi_Icc (a : ι → Real) :
    cubeDilation (fun i => (a i : WithTop Real)) =
      Set.univ.pi (fun i => Set.Icc (-(a i)) (a i)) := by
  ext x
  simp only [cubeDilation, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  constructor
  · intro h i
    exact abs_le.mp (WithTop.coe_le_coe.mp (h i))
  · intro h i
    exact WithTop.coe_le_coe.mpr (abs_le.mpr (h i))

theorem isCompact_cubeDilation (a : ι → Real) :
    IsCompact (cubeDilation fun i => (a i : WithTop Real)) := by
  rw [cubeDilation_eq_pi_Icc]
  exact isCompact_univ_pi fun i => isCompact_Icc

theorem relativelyCompact_cubeDilation (a : ι → Real) :
    IsCompact (closure (cubeDilation fun i => (a i : WithTop Real))) := by
  rw [(isCompact_cubeDilation a).isClosed.closure_eq]
  exact isCompact_cubeDilation a

/-- Mixed finite and `⊤` coefficients give proper regions with an unbounded
coordinate: "unbounded in one coordinate" alone does not force the whole ambient, so
the source's non-relative-compactness dichotomy needs the hull's rigidity beyond the
pure dilation form (candidate / needs-verification). -/
theorem exists_cubeDilation_mixed_coefficients :
    ∃ lam : Bool → WithTop Real,
      cubeDilation lam ≠ Set.univ ∧
        ∀ n : Nat, ∃ x ∈ cubeDilation lam, (n : Real) ≤ x true := by
  refine ⟨fun b => if b then ⊤ else 0, ?_, ?_⟩
  · intro h
    have h0 : (fun b : Bool => if b then (⊤ : WithTop Real) else 0) false = 0 := by
      simp
    have hp : (fun b : Bool => if b then (0 : Real) else 1) false ≠ 0 := by
      simp
    have hmem : (fun b : Bool => if b then (0 : Real) else 1) ∈
        cubeDilation (fun b : Bool => if b then (⊤ : WithTop Real) else 0) := by
      rw [h]
      exact Set.mem_univ _
    exact not_mem_cubeDilation_of_zero_coefficient
      (lam := fun b : Bool => if b then (⊤ : WithTop Real) else 0) h0 hp hmem
  · intro n
    refine ⟨fun b : Bool => if b then (n : Real) else 0, ?_, ?_⟩
    · intro b
      cases b <;> simp
    · simp

end HullLambdaDilation

end LeanFormal.IUT
