import tmp.sheaf.xif.paper.S1402HDDDependentSourceActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralHullSpan
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# S1418: consuming the dependent-place HDD source, actual hull/det

The S1402 source `S1402DependentHDDSource I s` supplies, for a finite set `s` of
rational finite places, an output-dependent allowed-image family

  `image : Theorem311Output I -> Set ((v : {v // v ∈ s}) -> Completion v)`

together with compactness, nonemptiness, coordinate nondegeneracy and the
`det (x) M` bookkeeping.  For an arbitrary source `D` this file

* builds the actual global HDD lattice `S1418GlobalLattice D o` as
  `LocalFieldProductHull.hull (D.image o)`, not as an arbitrary set;
* proves the actual hull facts: image inclusion, nonemptiness, idempotence,
  the exact `region lam` form with coordinatewise nonzero `lam`, the scaled
  unit-region form, and (under the explicit nonarchimedean hypothesis) the
  integral-span equality `span (integralRing hna) (closure (D.image o)) = hull`;
* consumes the source's actual `detData`: the `det (x) M` log-volume law on
  this lattice, including its two-fold iterate;
* proves that the source's placewise content is exactly a scaled unit ball
  (an `O_v`-lattice of rank one), via the place projection of the global hull;
* records the exact first field of the S1215 fourth joint,
  `S1215HDDLocalLattice (I := I)`, with no inhabitant.

The S1215 lattice at a place is a set of `Fin rank -> Completion v` tuples,
whereas the source supplies one `Completion v` factor at each place.  The
paper's HDD local lattice is the localization of an arithmetic vector bundle of
rank `> 1` (IUT III, Step (xi-d)); the source's dependent product is the
rank-one global region side.  No rank-one lattice, no constant/diagonal tuple
lattice and no arbitrary set is used as the first field.  Consequently this
file constructs the exact first field and does not assert an inhabitant of
`S1215HDDLocalLattice`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1418HDDConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual.S1402DependentHDDSource
open LeanFormal.IUT.LocalFieldProductHull

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-! ## 1. The actual global HDD lattice of the dependent source -/

/-- The actual global HDD lattice attached to a dependent-place source: the
smallest `lambda * O` region containing the source image, i.e. the actual
`LocalFieldProductHull.hull` of `D.image o`. -/
noncomputable def S1418GlobalLattice (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    Set ((v : {v // v ∈ s}) → S1402DependentE s v) :=
  D.dependentHull o

/-- The global lattice is exactly the actual product hull. -/
theorem s1418GlobalLattice_eq_hull (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    S1418GlobalLattice D o =
      @LocalFieldProductHull.hull {v // v ∈ s} (S1402DependentE s)
        (s1402DependentENormedField s) (D.image o) := rfl

/-- The source image is contained in its actual hull. -/
theorem s1418Image_subset_globalLattice (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    D.image o ⊆ S1418GlobalLattice D o :=
  subset_hull (D.image o)

/-- The actual hull of a nonempty source is nonempty. -/
theorem s1418GlobalLattice_nonempty (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) : (S1418GlobalLattice D o).Nonempty :=
  (D.nonempty o).mono (subset_hull (D.image o))

/-- The hull operation is monotone. -/
theorem s1418GlobalLattice_mono {D D' : S1402DependentHDDSource I s}
    (h : ∀ o, D.image o ⊆ D'.image o) (o : Theorem311Output I) :
    S1418GlobalLattice D o ⊆ S1418GlobalLattice D' o :=
  hull_mono (h o)

/-- The global lattice is a hull fixed point. -/
theorem s1418GlobalLattice_idempotent (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    hull (S1418GlobalLattice D o) = S1418GlobalLattice D o :=
  hull_idempotent (D.image o)

variable {ι : Type*} {K : ι → Type*} [∀ i, NormedField (K i)]

/-- Admissible scaled unit-ball regions are closed, without any properness
hypothesis. -/
theorem s1418IsClosed_region (lam : (i : ι) → K i) :
    IsClosed (region lam) := by
  have h : region lam = ⋂ i, {x : (i : ι) → K i | ‖x i‖ ≤ ‖lam i‖} := by
    ext x
    simp [region]
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_norm.comp (continuous_apply i)) continuous_const

/-- Passing to closure preserves the hull, because every admissible region is
closed.  This is the properness-free form of `hull_closure`. -/
theorem s1418Hull_closure_eq (S : Set ((i : ι) → K i)) :
    hull (closure S) = hull S := by
  refine Set.Subset.antisymm ?_ (hull_mono subset_closure)
  intro x hx lam hlam hS
  exact hx lam hlam (closure_minimal hS (s1418IsClosed_region lam))

/-- The actual hull of a relatively compact nondegenerate image is an actual
scaled ball region with nonzero scaling coefficients. -/
theorem s1418Exists_hull_eq_region_of_isCompact_closure
    {S : Set ((i : ι) → K i)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) :
    ∃ lam : (i : ι) → K i, (∀ i, lam i ≠ 0) ∧ hull S = region lam := by
  have hcoord' : ∀ i, ∃ x ∈ closure S, x i ≠ 0 := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hcoord i
    exact ⟨x, subset_closure hx, hxi⟩
  obtain ⟨lam, hlam, heq⟩ :=
    exists_hull_eq_region hS (hne.mono subset_closure) hcoord'
  exact ⟨lam, hlam, (s1418Hull_closure_eq S).symm.trans heq⟩

/-! ## 2. Actual hull facts for the dependent source -/

/-- The global lattice of any dependent source is an actual scaled ball region
with coordinatewise nonzero scaling vector. -/
theorem s1418GlobalLattice_eq_region (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    ∃ lam : (v : {v // v ∈ s}) → S1402DependentE s v,
      (∀ v, lam v ≠ 0) ∧ S1418GlobalLattice D o = region lam :=
  s1418Exists_hull_eq_region_of_isCompact_closure
    (S := D.image o) (D.compact_closure o) (D.nonempty o) (D.coordinate_nonzero o)

/-- In particular the global lattice is a multiplicative dilate of the actual
product of closed unit balls. -/
theorem s1418GlobalLattice_eq_smul_unitRegion (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    ∃ lam : (v : {v // v ∈ s}) → S1402DependentE s v,
      (∀ v, lam v ≠ 0) ∧
        S1418GlobalLattice D o = (fun x => lam * x) '' unitRegion := by
  obtain ⟨lam, hlam, heq⟩ := s1418GlobalLattice_eq_region D o
  exact ⟨lam, hlam, heq.trans (region_eq_mul_unitRegion lam hlam)⟩

/-- The realized hull region is the least region containing the source image. -/
theorem s1418GlobalLattice_least (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    ∃ lam : (v : {v // v ∈ s}) → S1402DependentE s v,
      (∀ v, lam v ≠ 0) ∧ S1418GlobalLattice D o = region lam ∧
        ∀ mu : (v : {v // v ∈ s}) → S1402DependentE s v,
          D.image o ⊆ region mu → region lam ⊆ region mu := by
  have hS : IsCompact (closure (D.image o)) := D.compact_closure o
  have hne : (closure (D.image o)).Nonempty := (D.nonempty o).mono subset_closure
  have hcoord : ∀ v, ∃ x ∈ closure (D.image o), x v ≠ 0 := by
    intro v
    obtain ⟨x, hx, hxv⟩ := D.coordinate_nonzero o v
    exact ⟨x, subset_closure hx, hxv⟩
  obtain ⟨lam, hlam, hsub, hleast⟩ := exists_least_region hS hne hcoord
  refine ⟨lam, hlam, ?_, ?_⟩
  · exact (s1418Hull_closure_eq (D.image o)).symm.trans
      (Set.Subset.antisymm (hull_minimal hlam hsub)
        (fun x hx mu _ hmu => hleast mu hmu hx))
  · intro mu hmu
    exact hleast mu (closure_minimal hmu (s1418IsClosed_region mu))

/-- The global lattice contains the origin. -/
theorem s1418GlobalLattice_zero_mem (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    (0 : (v : {v // v ∈ s}) → S1402DependentE s v) ∈
      S1418GlobalLattice D o := by
  obtain ⟨lam, _hlam, heq⟩ := s1418GlobalLattice_eq_region D o
  rw [heq]
  intro v
  simp

/-- The realizing scaling vector is a point of the lattice. -/
theorem s1418GlobalLattice_lam_mem (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    ∃ lam : (v : {v // v ∈ s}) → S1402DependentE s v,
      (∀ v, lam v ≠ 0) ∧ lam ∈ S1418GlobalLattice D o := by
  obtain ⟨lam, hlam, heq⟩ := s1418GlobalLattice_eq_region D o
  refine ⟨lam, hlam, ?_⟩
  rw [heq]
  intro v
  exact le_rfl

/-- For a nonempty place set the dependent HDD lattice is nontrivial: it
contains the origin and a nonzero point. -/
theorem s1418GlobalLattice_nontrivial (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) (hs : s.Nonempty) :
    (0 : (v : {v // v ∈ s}) → S1402DependentE s v) ∈ S1418GlobalLattice D o ∧
      ∃ x ∈ S1418GlobalLattice D o, x ≠ 0 := by
  obtain ⟨lam, hlam, heq⟩ := s1418GlobalLattice_eq_region D o
  obtain ⟨v0, hv0⟩ := hs
  refine ⟨?_, ⟨lam, ?_, ?_⟩⟩
  · rw [heq]
    intro v
    simp
  · rw [heq]
    intro v
    exact le_rfl
  · intro hzero
    exact hlam ⟨v0, hv0⟩ (congrFun hzero ⟨v0, hv0⟩)

/-- The actual integral span of the closure of the source image is the global
HDD lattice, under the nonarchimedean hypothesis required by the
`LocalFieldIntegralHull` donor. -/
theorem s1418IntegralSpan_eq_globalLattice (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I)
    (hna : ∀ v, IsNonarchimedean (Norm.norm : S1402DependentE s v → ℝ)) :
    (Submodule.span (integralRing hna) (closure (D.image o)) :
      Set ((v : {v // v ∈ s}) → S1402DependentE s v)) =
      S1418GlobalLattice D o := by
  have hS : IsCompact (closure (D.image o)) := D.compact_closure o
  have hne : (closure (D.image o)).Nonempty := (D.nonempty o).mono subset_closure
  have hcoord : ∀ v, ∃ x ∈ closure (D.image o), x v ≠ 0 := by
    intro v
    obtain ⟨x, hx, hxv⟩ := D.coordinate_nonzero o v
    exact ⟨x, subset_closure hx, hxv⟩
  have h := integralSpan_eq_hull hna hS hne hcoord
  rw [s1418Hull_closure_eq (D.image o)] at h
  exact h

/-! ## 3. The actual `det (x) M` bookkeeping on the dependent lattice -/

/-- The source's tensor-power exponent is a positive integer. -/
theorem s1418TensorPowerExponent_pos (D : S1402DependentHDDSource I s) :
    0 < D.detData.tensorPowerExponent :=
  D.detData.tensorPowerExponent_pos

/-- The actual `det (x) M` log-volume law applied to the global HDD lattice. -/
theorem s1418DetTensorPower_globalLattice (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    D.detData.logVolume (D.detData.detTensorPower (S1418GlobalLattice D o)) =
      (D.detData.tensorPowerExponent : ENNReal) *
        D.detData.logVolume (S1418GlobalLattice D o) :=
  D.detData.logVolume_detTensorPower _

/-- The actual `det (x) M` log-volume law on the source image. -/
theorem s1418DetTensorPower_image (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    D.detData.logVolume (D.detData.detTensorPower (D.image o)) =
      (D.detData.tensorPowerExponent : ENNReal) * D.detData.logVolume (D.image o) :=
  D.detData.logVolume_detTensorPower _

/-- The two-fold `det (x) M` iterate scales the log-volume by the square of
the tensor-power exponent. -/
theorem s1418DetTensorPower_two (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    D.detData.logVolume
        (D.detData.detTensorPower (D.detData.detTensorPower (S1418GlobalLattice D o))) =
      (D.detData.tensorPowerExponent : ENNReal) *
        (D.detData.tensorPowerExponent : ENNReal) *
        D.detData.logVolume (S1418GlobalLattice D o) := by
  rw [D.detData.logVolume_detTensorPower,
    D.detData.logVolume_detTensorPower]
  rw [mul_assoc]

/-- The actual frozen finite-packet hull/det specification holds.  This is the
det layer donor of the S1300/S1385 chain, consumed here as the actual
`det (x) M` source behind the bookkeeping field. -/
theorem s1418ActualFrozenHullDetSpec : HullDeterminantLogVolumeFrozenSpec :=
  hullDeterminantLogVolumeFrozenSpec_holds

/-! ## 4. The exact first field of the S1215 fourth joint -/

/-- Exact first field of `SourceSHEHDDCompatibility` (the S1215 fourth joint):
the HDD local lattice of common rank, with no inhabitant supplied.

The dependent source supplies one `Completion v` per place, not the
`Fin rank -> Completion v` tuples of this structure with `rank > 1`; hence the
first field stays exact. -/
abbrev S1418HDDLocalLatticeRequired (I : Input Label Choice) :=
  S1215HDDLocalLattice (I := I)

/-- The source's factor at a place is the 1-column local field itself, not a
power of it. -/
theorem s1418DependentE_eq_localField (v : {v // v ∈ s}) :
    S1402DependentE s v = (oneColumnStructure).localField v.1 := rfl

/-- The place projection of the actual global lattice. -/
noncomputable def S1418PlaceProjection (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) (v : {v // v ∈ s}) :
    Set (S1402DependentE s v) :=
  {y | ∃ x ∈ S1418GlobalLattice D o, x v = y}

/-- The place projection is exactly the actual scaled closed ball in the local
field: the source's placewise content is a rank-one `O_v`-lattice, not the
S1215 tuple lattice. -/
theorem s1418PlaceProjection_eq_closedBall (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    ∃ lam : (v : {v // v ∈ s}) → S1402DependentE s v,
      (∀ v, lam v ≠ 0) ∧ S1418GlobalLattice D o = region lam ∧
        ∀ v, S1418PlaceProjection D o v = Metric.closedBall 0 ‖lam v‖ := by
  classical
  obtain ⟨lam, hlam, heq⟩ := s1418GlobalLattice_eq_region D o
  refine ⟨lam, hlam, heq, fun v => ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ region lam := heq ▸ hx
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hx' v)
  · intro hy
    have hy' : ‖y‖ ≤ ‖lam v‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    refine ⟨Pi.single v y, ?_, ?_⟩
    · rw [heq]
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [Pi.single_eq_same] using hy'
      · simp [Pi.single_eq_of_ne hw]
    · exact Pi.single_eq_same v y

/-- The place projection contains the origin. -/
theorem s1418PlaceProjection_zero_mem (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) (v : {v // v ∈ s}) :
    (0 : S1402DependentE s v) ∈ S1418PlaceProjection D o v := by
  obtain ⟨lam, _hlam, heq⟩ := s1418GlobalLattice_eq_region D o
  refine ⟨0, ?_, rfl⟩
  rw [heq]
  intro w
  simp

/-- The place projection is nonempty. -/
theorem s1418PlaceProjection_nonempty (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) (v : {v // v ∈ s}) :
    (S1418PlaceProjection D o v).Nonempty :=
  ⟨0, s1418PlaceProjection_zero_mem D o v⟩

/-! ## 5. Donor checks -/

section DonorChecks

#check S1402DependentHDDSource
#check S1402DependentHDDSource.dependentHull
#check S1418GlobalLattice
#check s1418GlobalLattice_eq_hull
#check s1418GlobalLattice_eq_region
#check s1418GlobalLattice_eq_smul_unitRegion
#check s1418GlobalLattice_least
#check s1418IntegralSpan_eq_globalLattice
#check s1418DetTensorPower_globalLattice
#check s1418DetTensorPower_two
#check S1215HDDLocalLattice
#check S1418HDDLocalLatticeRequired I
#check s1418DependentE_eq_localField
#check s1418PlaceProjection_eq_closedBall
#check HullDeterminantLogVolumeFrozenSpec
#check DetTensorPowerLogVolumeBookkeeping
#check hullDeterminantLogVolumeFrozenSpec_holds
#check integralSpan_eq_hull

end DonorChecks

end LeanFormal.IUT.XiFPaper.S1418HDDConsumerActual

end