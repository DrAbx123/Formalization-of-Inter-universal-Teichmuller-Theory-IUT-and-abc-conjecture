import tmp.sheaf.xif.paper.NativeTateQSquaresBasicIntegrality

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateUnitOpenActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality
open IsDedekindDomain.HeightOneSpectrum

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

/-- In the nonarchimedean completion, `1 + z` has norm one when `‖z‖ < 1`. -/
theorem norm_one_add_of_norm_lt_one
    {z : localField (l := l) T b} (hz : ‖z‖ < 1) :
    ‖(1 : localField (l := l) T b) + z‖ = 1 := by
  have hle : ‖(1 : localField (l := l) T b) + z‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : localField (l := l) T b) z
    simpa [max_eq_left (le_of_lt hz)] using h
  have hge : 1 ≤ ‖(1 : localField (l := l) T b) + z‖ := by
    by_contra h
    have hlt : ‖(1 : localField (l := l) T b) + z‖ < 1 :=
      lt_of_not_ge h
    have hmax : max ‖(1 : localField (l := l) T b) + z‖ ‖z‖ < 1 :=
      max_lt hlt hz
    have h := IsUltrametricDist.norm_add_le_max
      ((1 : localField (l := l) T b) + z) (-z)
    have h1 : (1 : localField (l := l) T b) =
        ((1 : localField (l := l) T b) + z) + (-z) := by ring
    rw [← h1] at h
    have hle1 : (1 : ℝ) ≤ max
        ‖(1 : localField (l := l) T b) + z‖ ‖z‖ := by
      simpa using h
    exact (lt_irrefl (1 : ℝ)) (lt_of_le_of_lt hle1 hmax)
  exact le_antisymm hle hge

theorem one_add_mem_localRing
    {z : localField (l := l) T b} (hz : ‖z‖ < 1) :
    ((1 : localField (l := l) T b) + z) ∈ localRing (l := l) T b := by
  have hnorm : ‖(1 : localField (l := l) T b) + z‖ = 1 :=
    norm_one_add_of_norm_lt_one (l := l) T b hz
  exact (mem_adicCompletionIntegers
    (R := NumberField.RingOfIntegers T.arithmetic.F)
    (K := T.arithmetic.F)
    (v := localPrime (l := l) T b)).mpr
    ((Valued.toNormedField.norm_le_one_iff).mp (le_of_eq hnorm))

theorem one_add_inv_mem_localRing
    {z : localField (l := l) T b} (hz : ‖z‖ < 1) :
    ((1 : localField (l := l) T b) + z)⁻¹ ∈ localRing (l := l) T b := by
  have hnorm : ‖(1 : localField (l := l) T b) + z‖ = 1 :=
    norm_one_add_of_norm_lt_one (l := l) T b hz
  have hnorminv : ‖((1 : localField (l := l) T b) + z)⁻¹‖ = 1 := by
    rw [norm_inv, hnorm, inv_one]
  exact (mem_adicCompletionIntegers
    (R := NumberField.RingOfIntegers T.arithmetic.F)
    (K := T.arithmetic.F)
    (v := localPrime (l := l) T b)).mpr
    ((Valued.toNormedField.norm_le_one_iff).mp (le_of_eq hnorminv))

/-- One plus a norm-small element is a unit of the completion integers. -/
theorem one_add_isUnit
    {z : localField (l := l) T b} (hz : ‖z‖ < 1) :
    ∃ u : localRing (l := l) T b,
      IsUnit u ∧ (u : localField (l := l) T b) =
        (1 : localField (l := l) T b) + z := by
  let u : localRing (l := l) T b :=
    ⟨(1 : localField (l := l) T b) + z,
      one_add_mem_localRing (l := l) T b hz⟩
  let v : localRing (l := l) T b :=
    ⟨((1 : localField (l := l) T b) + z)⁻¹,
      one_add_inv_mem_localRing (l := l) T b hz⟩
  have hnorm : ‖(1 : localField (l := l) T b) + z‖ = 1 :=
    norm_one_add_of_norm_lt_one (l := l) T b hz
  have hne : ((1 : localField (l := l) T b) + z) ≠ 0 := by
    intro hzero
    have := hnorm
    rw [hzero, norm_zero] at this
    norm_num at this
  have h1 : u * v = 1 := by
    apply Subtype.ext
    change ((1 : localField (l := l) T b) + z) *
      ((1 : localField (l := l) T b) + z)⁻¹ = 1
    field_simp [hne]
  have h2 : v * u = 1 := by
    apply Subtype.ext
    change ((1 : localField (l := l) T b) + z)⁻¹ *
      ((1 : localField (l := l) T b) + z) = 1
    field_simp [hne]
  refine ⟨u, ?_, rfl⟩
  exact ⟨⟨u, v, h1, h2⟩, rfl⟩

/-- A ball of radius one around a unit stays inside the unit set. -/
theorem unit_ball_subset
    {u : localRing (l := l) T b} (hu : IsUnit u)
    {y : localField (l := l) T b}
    (hy : ‖y - (u : localField (l := l) T b)‖ < 1) :
    ∃ w : localRing (l := l) T b,
      IsUnit w ∧ (w : localField (l := l) T b) = y := by
  have hcoe_inv : ((((hu.unit)⁻¹ : (localRing (l := l) T b)ˣ) : localRing (l := l) T b) :
      localField (l := l) T b) = (u : localField (l := l) T b)⁻¹ := by
    calc
      ((((hu.unit)⁻¹ : (localRing (l := l) T b)ˣ) :
          localRing (l := l) T b) : localField (l := l) T b) =
          ((((hu.unit : localRing (l := l) T b) :
            localField (l := l) T b)))⁻¹ := by
            exact map_units_inv (algebraMap (localRing (l := l) T b)
              (localField (l := l) T b)) hu.unit
      _ = (u : localField (l := l) T b)⁻¹ := by
            rw [hu.unit_spec]
  have hinv_le : ‖(u : localField (l := l) T b)⁻¹‖ ≤ 1 := by
    rw [← hcoe_inv]
    exact (Valued.toNormedField.norm_le_one_iff).mpr
      ((mem_adicCompletionIntegers
        (R := NumberField.RingOfIntegers T.arithmetic.F)
        (K := T.arithmetic.F)
        (v := localPrime (l := l) T b)).mp
        ((((hu.unit)⁻¹ : (localRing (l := l) T b)ˣ) : localRing (l := l) T b).property))
  let w : localField (l := l) T b :=
    (u : localField (l := l) T b)⁻¹ *
      (y - (u : localField (l := l) T b))
  have hw : ‖w‖ < 1 := by
    calc
      ‖w‖ = ‖(u : localField (l := l) T b)⁻¹ *
          (y - (u : localField (l := l) T b))‖ := rfl
      _ ≤ ‖(u : localField (l := l) T b)⁻¹‖ *
          ‖y - (u : localField (l := l) T b)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖y - (u : localField (l := l) T b)‖ := by
        gcongr
      _ < 1 := by simpa using hy
  rcases one_add_isUnit (l := l) T b hw with ⟨v, hv, hv_eq⟩
  have huK : IsUnit (u : localField (l := l) T b) :=
    hu.map (algebraMap (localRing (l := l) T b) (localField (l := l) T b))
  have hune : (u : localField (l := l) T b) ≠ 0 := huK.ne_zero
  have hprod : ((u * v : localRing (l := l) T b) :
      localField (l := l) T b) = y := by
    change (u : localField (l := l) T b) *
      (v : localField (l := l) T b) = y
    rw [hv_eq]
    change (u : localField (l := l) T b) *
      ((1 : localField (l := l) T b) +
        (u : localField (l := l) T b)⁻¹ *
          (y - (u : localField (l := l) T b))) = y
    field_simp [hune]
    ring
  exact ⟨u * v, hu.mul hv, hprod⟩

/-- Units of the completion integers, as a subset of the completion. -/
noncomputable def unitKSet : Set (localField (l := l) T b) :=
  {x | ∃ u : localRing (l := l) T b,
    IsUnit u ∧ (u : localField (l := l) T b) = x}

/-- Every unit ball of radius one is contained in the unit set. -/
theorem unitKSet_isOpen :
    IsOpen (unitKSet (l := l) T b) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨u, hu, rfl⟩
  have hball : Metric.ball (u : localField (l := l) T b) 1 ⊆
      unitKSet (l := l) T b := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact unit_ball_subset (l := l) T b hu (by
      simpa [norm_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy)
  exact Filter.mem_of_superset (Metric.ball_mem_nhds _ zero_lt_one) hball

/-- Maximal ideal of the completion integers, as local integral elements
minus the units.  This avoids the existential subtype image. -/
noncomputable def maximalIdealKSet : Set (localField (l := l) T b) :=
  (localRing (l := l) T b : Set (localField (l := l) T b)) ∩
    (unitKSet (l := l) T b)ᶜ

theorem maximalIdealKSet_isClosed :
    IsClosed (maximalIdealKSet (l := l) T b) :=
  (localRing_isClosed (l := l) T b).inter
    (unitKSet_isOpen (l := l) T b).isClosed_compl

theorem tsum_mem_maximalIdeal
    {f : ℕ → localRing (l := l) T b}
    (hf : ∀ n, f n ∈ IsLocalRing.maximalIdeal (localRing (l := l) T b))
    {x : localField (l := l) T b}
    (hsum : HasSum (fun n => (f n : localField (l := l) T b)) x) :
    x ∈ maximalIdealKSet (l := l) T b := by
  let s : ℕ → localRing (l := l) T b := fun N =>
    (Finset.range N).sum (fun n => f n)
  have hs : ∀ N, s N ∈ IsLocalRing.maximalIdeal (localRing (l := l) T b) := by
    intro N
    dsimp [s]
    exact Ideal.sum_mem (IsLocalRing.maximalIdeal (localRing (l := l) T b))
      (t := Finset.range N) (fun n _ => hf n)
  have hconv : Filter.Tendsto
      (fun N : ℕ => (s N : localField (l := l) T b))
      Filter.atTop (nhds x) := by
    simpa [s, map_sum] using hsum.tendsto_sum_nat
  have hxR : x ∈ localRing (l := l) T b :=
    (localRing_isClosed (l := l) T b).mem_of_tendsto hconv
      (Filter.Eventually.of_forall fun N => (s N).property)
  have hxnotunit : x ∉ unitKSet (l := l) T b := by
    intro hxunit
    have hev : ∀ᶠ N in Filter.atTop,
        (s N : localField (l := l) T b) ∈ unitKSet (l := l) T b :=
      hconv.eventually ((unitKSet_isOpen (l := l) T b).mem_nhds hxunit)
    rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
    rcases hN N le_rfl with ⟨u, hu, hux⟩
    have hnonunit : ¬ IsUnit (s N) := by
      rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
      exact hs N
    have hug : u = s N := Subtype.ext hux
    exact hnonunit (hug ▸ hu)
  exact ⟨hxR, hxnotunit⟩

end LeanFormal.IUT.XiFPaper.NativeTateUnitOpenActual

end
