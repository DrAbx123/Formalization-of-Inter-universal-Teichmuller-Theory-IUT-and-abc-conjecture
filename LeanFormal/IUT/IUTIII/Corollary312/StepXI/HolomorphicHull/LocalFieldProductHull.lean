import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Smallest coordinatewise `lambda * O` regions in products of local fields

Analytic prerequisite for IUT III Remark 3.9.5(i),(ii), consumed by the
N4--N7 source hull problem. Unlike a multiplicative submonoid closed under all
scalings, a region here is the multiplicative image of the product of closed
unit balls. Compactness supplies the coordinate maxima; no boundedness or
leastness assertion is stored as an unproved data field.

The result applies to any finite family of proper normed fields. In the
nonarchimedean case the closed unit balls are the rings of integers; in the
complex case they are the closed unit discs. The source IQ decomposition,
its identification with such a product, and compactness of the actual theta
images are separate prerequisites, not conclusions of this module.

The nondegeneracy hypothesis is coordinatewise: each projection of the region
contains a nonzero element. This is needed for the paper's nonzero scaling
coefficients. A singleton at zero does not have a smallest nonzero-radius disc.
-/

open Metric MeasureTheory
open scoped Pointwise

namespace LeanFormal.IUT.LocalFieldProductHull

variable {ι : Type*} {K : ι → Type*} [∀ i, NormedField (K i)]

/-- Product of the closed unit balls (the holomorphic integral structure). -/
def unitRegion : Set ((i : ι) → K i) := {x | ∀ i, ‖x i‖ ≤ 1}

/-- Product of the discs with radii given by the norms of `lam`. -/
def region (lam : (i : ι) → K i) : Set ((i : ι) → K i) :=
  {x | ∀ i, ‖x i‖ ≤ ‖lam i‖}

/-- These discs really are multiplicative dilates, not translation models. -/
theorem region_eq_mul_unitRegion (lam : (i : ι) → K i)
    (hlam : ∀ i, lam i ≠ 0) :
    region lam = (fun x => lam * x) '' unitRegion (K := K) := by
  ext x
  constructor
  · intro hx
    refine ⟨fun i => x i / lam i, ?_, ?_⟩
    · intro i
      rw [norm_div, div_le_one (norm_pos_iff.mpr (hlam i))]
      exact hx i
    · funext i
      exact mul_div_cancel₀ (x i) (hlam i)
  · rintro ⟨y, hy, rfl⟩ i
    change ‖lam i * y i‖ ≤ ‖lam i‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hy i)

/-- A compact set has a simultaneous coordinate maximum represented by a
scaling vector. The maximum in different coordinates may occur at different points. -/
theorem exists_coordinate_maxima {S : Set ((i : ι) → K i)}
    (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ lam : (i : ι) → K i,
      (∀ i, ∃ x ∈ S, lam i = x i) ∧ S ⊆ region lam := by
  have hmax : ∀ i, ∃ x ∈ S, ∀ y ∈ S, ‖y i‖ ≤ ‖x i‖ := by
    intro i
    exact hS.exists_isMaxOn hne (continuous_norm.comp (continuous_apply i)).continuousOn
  choose maximizer hmem hbound using hmax
  exact ⟨fun i => maximizer i i, fun i => ⟨maximizer i, hmem i, rfl⟩,
    fun _ hx i => hbound i _ hx⟩

/-- The paper's smallest `lambda * O` region exists for every compact region
with nonzero coordinate projections. No source IQ realization is assumed here. -/
theorem exists_least_region {S : Set ((i : ι) → K i)}
    (hS : IsCompact S) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) :
    ∃ lam : (i : ι) → K i, (∀ i, lam i ≠ 0) ∧ S ⊆ region lam ∧
      ∀ mu : (i : ι) → K i, S ⊆ region mu → region lam ⊆ region mu := by
  obtain ⟨lam, hrealized, hbound⟩ := exists_coordinate_maxima hS hne
  refine ⟨lam, ?_, hbound, ?_⟩
  · intro i
    obtain ⟨x, hx, hxi⟩ := hcoord i
    exact norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hxi) (hbound hx i))
  · intro mu hmu x hx i
    obtain ⟨w, hw, hwi⟩ := hrealized i
    exact le_trans (hx i) (by rw [hwi]; exact hmu hw i)

/-- The least region is independent of the maximizing witnesses. -/
theorem least_region_unique {S : Set ((i : ι) → K i)}
    {lam mu : (i : ι) → K i}
    (hlam : S ⊆ region lam) (hmu : S ⊆ region mu)
    (hleastLam : ∀ nu, S ⊆ region nu → region lam ⊆ region nu)
    (hleastMu : ∀ nu, S ⊆ region nu → region mu ⊆ region nu) :
    region lam = region mu :=
  Set.Subset.antisymm (hleastLam mu hmu) (hleastMu lam hlam)

/-- The unit region is genuinely compact in finite products of proper fields. -/
theorem isCompact_unitRegion [Finite ι] [∀ i, ProperSpace (K i)] :
    IsCompact (unitRegion (K := K)) := by
  have heq : unitRegion (K := K) = Set.pi Set.univ (fun i => closedBall (0 : K i) 1) := by
    ext x
    simp [unitRegion, Set.mem_pi, mem_closedBall, dist_zero_right]
  rw [heq]
  exact isCompact_univ_pi (fun i => isCompact_closedBall (0 : K i) 1)

/-- Every coordinate disc product, including degenerate discs, is compact. -/
theorem isCompact_region [Finite ι] [∀ i, ProperSpace (K i)] (lam : (i : ι) → K i) :
    IsCompact (region lam) := by
  have heq : region lam = Set.pi Set.univ (fun i => closedBall (0 : K i) ‖lam i‖) := by
    ext x
    simp [region, Set.mem_pi, mem_closedBall, dist_zero_right]
  rw [heq]
  exact isCompact_univ_pi (fun i => isCompact_closedBall (0 : K i) ‖lam i‖)

/-- Finiteness uses compactness and local finiteness, without a false invariance
under multiplicative scaling. This includes additive Haar measures. -/
theorem measure_region_lt_top [Finite ι] [∀ i, ProperSpace (K i)]
    [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) [IsFiniteMeasureOnCompacts μ]
    (lam : (i : ι) → K i) : μ (region lam) < ⊤ :=
  (isCompact_region lam).measure_lt_top

/-- The region is the intersection of all coordinate disc products containing
the input, matching the intersection characterization of Remark 3.9.5(ii). -/
theorem least_region_eq_intersection {S : Set ((i : ι) → K i)}
    {lam : (i : ι) → K i} (hsub : S ⊆ region lam)
    (hleast : ∀ mu, S ⊆ region mu → region lam ⊆ region mu) :
    region lam = {x | ∀ mu, S ⊆ region mu → x ∈ region mu} := by
  ext x
  exact ⟨fun hx mu hmu => hleast mu hmu hx, fun hx => hx lam hsub⟩

/-- Intersection of the paper's admissible nonzero coordinate dilates.
Outside the relatively compact, nondegenerate domain it need not itself be
an admissible region; the lemmas below state the exact domain of that conclusion. -/
def hull (S : Set ((i : ι) → K i)) : Set ((i : ι) → K i) :=
  {x | ∀ lam : (i : ι) → K i, (∀ i, lam i ≠ 0) → S ⊆ region lam → x ∈ region lam}

theorem subset_hull (S : Set ((i : ι) → K i)) : S ⊆ hull S :=
  fun _ hx _ _ hsub => hsub hx

theorem hull_minimal {S : Set ((i : ι) → K i)} {lam : (i : ι) → K i}
    (hlam : ∀ i, lam i ≠ 0) (hsub : S ⊆ region lam) : hull S ⊆ region lam :=
  fun _ hx => hx lam hlam hsub

theorem hull_mono {S T : Set ((i : ι) → K i)} (hST : S ⊆ T) : hull S ⊆ hull T :=
  fun _ hx lam hlam hT => hx lam hlam (hST.trans hT)

theorem hull_region (lam : (i : ι) → K i) (hlam : ∀ i, lam i ≠ 0) :
    hull (region lam) = region lam :=
  Set.Subset.antisymm (hull_minimal hlam subset_rfl) (subset_hull _)

theorem hull_idempotent (S : Set ((i : ι) → K i)) : hull (hull S) = hull S := by
  apply Set.Subset.antisymm
  · intro x hx lam hlam hS
    exact hx lam hlam (hull_minimal hlam hS)
  · exact subset_hull _

/-- The intersection is an actual nonzero `lambda * O` region, proved from
compactness and nondegeneracy rather than postulated as a source field. -/
theorem exists_hull_eq_region {S : Set ((i : ι) → K i)}
    (hS : IsCompact S) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) :
    ∃ lam : (i : ι) → K i, (∀ i, lam i ≠ 0) ∧ hull S = region lam := by
  obtain ⟨lam, hlam, hsub, hleast⟩ := exists_least_region hS hne hcoord
  exact ⟨lam, hlam, Set.Subset.antisymm (hull_minimal hlam hsub)
    (fun _ hx mu _ hmu => hleast mu hmu hx)⟩

/-- Passing to closure does not change the hull because the candidate regions
are closed. This gives the relatively compact version of the construction. -/
theorem hull_closure [Finite ι] [∀ i, ProperSpace (K i)]
    (S : Set ((i : ι) → K i)) : hull (closure S) = hull S := by
  apply Set.Subset.antisymm
  · intro x hx lam hlam hS
    exact hx lam hlam (closure_minimal hS (isCompact_region lam).isClosed)
  · exact hull_mono subset_closure

/-- Relatively compact input with nonzero coordinate projections has an
admissible hull, even when the input itself is not closed. -/
theorem exists_hull_eq_region_of_isCompact_closure [Finite ι] [∀ i, ProperSpace (K i)]
    {S : Set ((i : ι) → K i)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) :
    ∃ lam : (i : ι) → K i, (∀ i, lam i ≠ 0) ∧ hull S = region lam := by
  have hcoordClosure : ∀ i, ∃ x ∈ closure S, x i ≠ 0 := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hcoord i
    exact ⟨x, subset_closure hx, hxi⟩
  simpa only [hull_closure] using
    exists_hull_eq_region hS (hne.mono subset_closure) hcoordClosure

/-- The whole-ambient branch in Remark 3.9.5(i) follows from the same
intersection definition: no compact coordinate region can contain this input. -/
theorem hull_eq_univ_of_not_isCompact_closure [Finite ι] [∀ i, ProperSpace (K i)]
    {S : Set ((i : ι) → K i)} (hS : ¬ IsCompact (closure S)) : hull S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x lam _ hsub
  exact False.elim (hS ((isCompact_region lam).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isCompact_region lam).isClosed)))

/-- Actual finite Haar mass of the relatively compact hull. No scaling
contraction, global degree bound, or value-monoid realization is needed. -/
theorem measure_hull_lt_top [Finite ι] [∀ i, ProperSpace (K i)]
    [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) [IsFiniteMeasureOnCompacts μ]
    {S : Set ((i : ι) → K i)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) : μ (hull S) < ⊤ := by
  obtain ⟨lam, _, heq⟩ := exists_hull_eq_region_of_isCompact_closure hS hne hcoord
  rw [heq]
  exact measure_region_lt_top μ lam

/-- A nonzero coordinate dilation contains a neighborhood of zero. Finiteness
of the index is essential here, unlike compactness of the product of discs. -/
theorem zero_mem_interior_region [Finite ι] (lam : (i : ι) → K i)
    (hlam : ∀ i, lam i ≠ 0) : (0 : (i : ι) → K i) ∈ interior (region lam) := by
  have hopen : IsOpen {x : (i : ι) → K i | ∀ i, ‖x i‖ < ‖lam i‖} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have hzero : (0 : (i : ι) → K i) ∈
      {x : (i : ι) → K i | ∀ i, ‖x i‖ < ‖lam i‖} := by
    intro i
    simpa only [Pi.zero_apply, norm_zero] using norm_pos_iff.mpr (hlam i)
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hopen.mem_nhds hzero) (fun _ hx i => (hx i).le))

theorem measure_region_pos [Finite ι] [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) [Measure.IsOpenPosMeasure μ]
    (lam : (i : ι) → K i) (hlam : ∀ i, lam i ≠ 0) : 0 < μ (region lam) :=
  Measure.measure_pos_of_nonempty_interior μ ⟨0, zero_mem_interior_region lam hlam⟩

/-- A nondegenerate relatively compact hull has positive finite mass. Hence
the real logarithm here is the logarithm of an actual positive finite volume. -/
theorem measure_hull_pos_lt_top [Finite ι] [∀ i, ProperSpace (K i)]
    [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {S : Set ((i : ι) → K i)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) : 0 < μ (hull S) ∧ μ (hull S) < ⊤ := by
  obtain ⟨lam, hlam, heq⟩ := exists_hull_eq_region_of_isCompact_closure hS hne hcoord
  rw [heq]
  exact ⟨measure_region_pos μ lam hlam, measure_region_lt_top μ lam⟩

/-- Signed log of Haar mass relative to the unit region. The value is used as
a log-volume only on positive finite-mass regions, as in the next lemmas.
This is the unweighted local expression; residue-degree/packet weights and
source poly-isomorphisms are not supplied by this definition. -/
noncomputable def normalizedLogVolume [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) (S : Set ((i : ι) → K i)) : ℝ :=
  Real.log (μ S).toReal - Real.log (μ (unitRegion (K := K))).toReal

theorem normalizedLogVolume_unitRegion [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) :
    normalizedLogVolume μ (unitRegion (K := K)) = 0 := sub_self _

/-- The monotonicity step uses positive finite masses, so neither zero nor
infinite mass is silently turned into a finite log-volume. -/
theorem normalizedLogVolume_mono [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) {S T : Set ((i : ι) → K i)}
    (hST : S ⊆ T) (hS : 0 < μ S) (hT : μ T < ⊤) :
    normalizedLogVolume μ S ≤ normalizedLogVolume μ T := by
  have hSfin : μ S < ⊤ := lt_of_le_of_lt (measure_mono hST) hT
  apply sub_le_sub_right
  exact Real.log_le_log (ENNReal.toReal_pos hS.ne' hSfin.ne)
    (ENNReal.toReal_mono hT.ne (measure_mono hST))

/-- The source image-to-hull lower-bound transfer with a signed real volume,
under its precise analytic hypotheses. The source image's positive mass
remains an explicit prerequisite; it is not inferred from mere nonemptiness. -/
theorem normalizedLogVolume_le_hull [Finite ι] [∀ i, ProperSpace (K i)]
    [MeasurableSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) [IsFiniteMeasureOnCompacts μ]
    {S : Set ((i : ι) → K i)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) (hpos : 0 < μ S) :
    normalizedLogVolume μ S ≤ normalizedLogVolume μ (hull S) :=
  normalizedLogVolume_mono μ (subset_hull S) hpos (measure_hull_lt_top μ hS hne hcoord)

/-- Finite unions of continuous compact images supply the compactness needed
by the hull construction. This is the shape of the finitely labeled `U_j`;
the continuous source maps still have to be constructed at the use site. -/
theorem isCompact_union_images {J : Type*} [Finite J] {A : J → Type*}
    [∀ j, TopologicalSpace (A j)] (C : (j : J) → Set (A j))
    (hC : ∀ j, IsCompact (C j)) (f : (j : J) → A j → (i : ι) → K i)
    (hf : ∀ j, ContinuousOn (f j) (C j)) :
    IsCompact (⋃ j, f j '' C j) :=
  isCompact_iUnion fun j => (hC j).image_of_continuousOn (hf j)

/-- One nonzero point in each coordinate can be supplied at different labels.
The conclusion is the paper's actual multiplicative hull, not a submonoid
closed under all nonzero scalings. -/
theorem exists_union_images_hull_eq_mul_unitRegion
    {J : Type*} [Finite J] {A : J → Type*} [∀ j, TopologicalSpace (A j)]
    (C : (j : J) → Set (A j)) (hC : ∀ j, IsCompact (C j))
    (f : (j : J) → A j → (i : ι) → K i) (hf : ∀ j, ContinuousOn (f j) (C j))
    (hne : (⋃ j, f j '' C j).Nonempty)
    (hcoord : ∀ i, ∃ j, ∃ x ∈ C j, f j x i ≠ 0) :
    ∃ lam : (i : ι) → K i, (∀ i, lam i ≠ 0) ∧
      hull (⋃ j, f j '' C j) = (fun x => lam * x) '' unitRegion (K := K) := by
  have hnonzero : ∀ i, ∃ x ∈ ⋃ j, f j '' C j, x i ≠ 0 := by
    intro i
    obtain ⟨j, x, hx, hxi⟩ := hcoord i
    exact ⟨f j x, Set.mem_iUnion.mpr ⟨j, ⟨x, hx, rfl⟩⟩, hxi⟩
  obtain ⟨lam, hlam, heq⟩ := exists_hull_eq_region
    (isCompact_union_images C hC f hf) hne hnonzero
  exact ⟨lam, hlam, heq.trans (region_eq_mul_unitRegion lam hlam)⟩

/-- Compactness of an integral span over a compact coefficient ring, used
before tensor packet field decomposition. Finite generation is the exact
algebraic prerequisite, not a postulated compactness field. -/
theorem isCompact_finite_integralSpan {R : Type*} [CommSemiring R]
    [TopologicalSpace R] [CompactSpace R] {E : Type*} [AddCommMonoid E]
    [Module R E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul R E]
    (generators : Finset E) :
    IsCompact (Submodule.span R (generators : Set E) : Set E) :=
  Submodule.isCompact_of_fg (Submodule.fg_span (R := R) generators.finite_toSet)

/-- Nonzero coordinate multipliers regarded as actual field units. -/
def scalingUnits (lam : (i : ι) → K i) (hlam : ∀ i, lam i ≠ 0) : (i : ι) → (K i)ˣ :=
  fun i => Units.mk0 (lam i) (hlam i)

/-- The group action used by the Haar character is exactly the multiplication
action defining the paper's regions. -/
theorem scalingUnits_smul_unitRegion (lam : (i : ι) → K i) (hlam : ∀ i, lam i ≠ 0) :
    scalingUnits lam hlam • unitRegion (K := K) = region lam := by
  rw [region_eq_mul_unitRegion lam hlam]
  rfl

/-- Exact signed log-volume transformation under multiplicative dilation.
The change is the log of the distributive Haar character, not zero in general.
This proves the scaling law from Haar uniqueness; no source normalization
equation or invariance under arbitrary field multiplication is postulated. -/
theorem normalizedLogVolume_smul [Finite ι] [∀ i, ProperSpace (K i)]
    [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) [Measure.IsAddHaarMeasure μ]
    (g : (i : ι) → (K i)ˣ) {S : Set ((i : ι) → K i)}
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    normalizedLogVolume μ (g • S) =
      Real.log (distribHaarChar ((i : ι) → K i) g : ℝ) + normalizedLogVolume μ S := by
  have hchar : (distribHaarChar ((i : ι) → K i) g : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := (i : ι) → K i) (g := g)).ne'
  unfold normalizedLogVolume
  rw [← distribHaarChar_mul μ g S, ENNReal.toReal_mul, ENNReal.coe_toReal,
    Real.log_mul hchar (ENNReal.toReal_pos hpos.ne' hfin.ne).ne']
  exact add_sub_assoc _ _ _

/-- In particular the log-volume of `lambda * O` is the logarithmic Haar
character of `lambda`, with `O` as the zero of the normalization. -/
theorem normalizedLogVolume_region [Finite ι] [∀ i, ProperSpace (K i)]
    [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
    (μ : Measure ((i : ι) → K i)) [Measure.IsAddHaarMeasure μ]
    (lam : (i : ι) → K i) (hlam : ∀ i, lam i ≠ 0) :
    normalizedLogVolume μ (region lam) =
      Real.log (distribHaarChar ((i : ι) → K i) (scalingUnits lam hlam) : ℝ) := by
  have hunit : unitRegion (K := K) = region (1 : (i : ι) → K i) := by
    ext x
    simp [unitRegion, region]
  have hpos : 0 < μ (unitRegion (K := K)) := by
    rw [hunit]
    exact measure_region_pos μ 1 (fun _ => one_ne_zero)
  have hfin : μ (unitRegion (K := K)) < ⊤ := isCompact_unitRegion.measure_lt_top
  simpa only [scalingUnits_smul_unitRegion, normalizedLogVolume_unitRegion, add_zero] using
    normalizedLogVolume_smul μ (scalingUnits lam hlam) hpos hfin

end LeanFormal.IUT.LocalFieldProductHull
