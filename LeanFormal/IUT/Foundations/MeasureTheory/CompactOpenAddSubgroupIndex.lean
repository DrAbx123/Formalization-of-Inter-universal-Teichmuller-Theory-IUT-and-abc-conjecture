import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Relative Haar mass from the two intersection indices

Two compact open additive subgroups are commensurable. Their actual
quotients by their intersection are finite, and the difference of their
logarithmic Haar masses is the difference of the logarithms of these
two finite indices. No containment between the two subgroups is assumed.
-/

namespace LeanFormal.IUT.CompactOpenAddSubgroup

open MeasureTheory

noncomputable section

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable (H K : AddSubgroup G)

def intersectionInLeft : AddSubgroup H := K.comap H.subtype

def intersectionIndex : ℕ := Nat.card (H ⧸ intersectionInLeft H K)

omit [IsTopologicalAddGroup G] in
theorem isOpen_intersectionInLeft (hK : IsOpen (K : Set G)) :
    IsOpen (intersectionInLeft H K : Set H) :=
  hK.preimage continuous_subtype_val

theorem finite_intersectionQuotient (hH : IsCompact (H : Set G))
    (hK : IsOpen (K : Set G)) : Finite (H ⧸ intersectionInLeft H K) := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  letI := QuotientAddGroup.discreteTopology (N := intersectionInLeft H K)
    (isOpen_intersectionInLeft H K hK)
  exact finite_of_compact_of_discrete

theorem intersectionIndex_pos (hH : IsCompact (H : Set G))
    (hK : IsOpen (K : Set G)) : 0 < intersectionIndex H K := by
  letI := finite_intersectionQuotient H K hH hK
  exact Nat.card_pos

variable [MeasurableSpace G] [BorelSpace G]

theorem measure_eq_index_mul_intersection (hHcompact : IsCompact (H : Set G))
    (hHopen : IsOpen (H : Set G)) (hKopen : IsOpen (K : Set G))
    (μ : Measure G) [Measure.IsAddHaarMeasure μ] :
    μ (H : Set G) = (intersectionIndex H K : ENNReal) * μ ((H : Set G) ∩ K) := by
  let subgroupMeasure := μ.comap (H.subtype : H → G)
  have embedding : Topology.IsOpenEmbedding (H.subtype : H → G) :=
    hHopen.isOpenEmbedding_subtypeVal
  letI : Measure.IsAddHaarMeasure subgroupMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ embedding
  letI : (intersectionInLeft H K).FiniteIndex := ⟨by
    rw [AddSubgroup.index_eq_card]
    exact (intersectionIndex_pos H K hHcompact hKopen).ne'⟩
  have hmeasure (S : Set H) : subgroupMeasure S = μ (H.subtype '' S) :=
    embedding.measurableEmbedding.comap_apply μ S
  have hintersection : H.subtype '' (intersectionInLeft H K : Set H) =
      (H : Set G) ∩ K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hH, hK⟩
      exact ⟨⟨x, hH⟩, hK, rfl⟩
  have hwhole : H.subtype '' (Set.univ : Set H) = (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have hindex := MeasureTheory.AddSubgroup.index_mul_measure (intersectionInLeft H K)
    (isOpen_intersectionInLeft H K hKopen).measurableSet subgroupMeasure
  simp only [hmeasure, hintersection, hwhole, AddSubgroup.index_eq_card] at hindex
  exact hindex.symm

theorem relative_log_measure_eq_log_indices
    (hHcompact : IsCompact (H : Set G)) (hKcompact : IsCompact (K : Set G))
    (hHopen : IsOpen (H : Set G)) (hKopen : IsOpen (K : Set G))
    (μ : Measure G) [Measure.IsAddHaarMeasure μ] :
    Real.log (μ (H : Set G)).toReal - Real.log (μ (K : Set G)).toReal =
      Real.log (intersectionIndex H K : ℝ) - Real.log (intersectionIndex K H : ℝ) := by
  have hmasspos : 0 < μ ((H : Set G) ∩ K) :=
    Measure.measure_pos_of_nonempty_interior μ (by
      rw [(hHopen.inter hKopen).interior_eq]
      exact ⟨0, H.zero_mem, K.zero_mem⟩)
  have hmassfinite : μ ((H : Set G) ∩ K) < ⊤ :=
    (measure_mono Set.inter_subset_left).trans_lt hHcompact.measure_lt_top
  have hmassnonzero := (ENNReal.toReal_pos hmasspos.ne' hmassfinite.ne).ne'
  have hleft : (intersectionIndex H K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (intersectionIndex_pos H K hHcompact hKopen).ne'
  have hright : (intersectionIndex K H : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (intersectionIndex_pos K H hKcompact hHopen).ne'
  rw [measure_eq_index_mul_intersection H K hHcompact hHopen hKopen,
    measure_eq_index_mul_intersection K H hKcompact hKopen hHopen,
    Set.inter_comm (K : Set G) (H : Set G)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [Real.log_mul hleft hmassnonzero, Real.log_mul hright hmassnonzero]
  ring

end

end LeanFormal.IUT.CompactOpenAddSubgroup
