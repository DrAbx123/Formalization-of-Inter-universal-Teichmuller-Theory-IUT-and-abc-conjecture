import LeanFormal.IUT.Foundations.LocalFields.FiniteLocalSubfieldCofinality
import LeanFormal.IUT.Foundations.LocalFields.UnitPerfectionMapTopology

/-!
# Cofinality for the actual unit-perfection ind topology

Restricting to finite local fields containing a fixed finite base does
not change the source final topology. The proof uses continuous maps of
the original unit perfections and their actual composition law.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]

abbrev algebraicUnitPerfectionIndTopologyAbove (B : FiniteLocalSubfield p Ω) :
    TopologicalSpace (UnitLogPerfection Ω) :=
  ⨆ F : FiniteLocalSubfieldAbove B, TopologicalSpace.coinduced
    (unitPerfectionMap F.val.val.val.toRingHom
      (isometry_intermediateField_inclusion F.val.val))
    (unitPerfectionTopology F.val.val)

theorem isOpen_algebraicUnitPerfectionIndTopologyAbove_iff
    (B : FiniteLocalSubfield p Ω) (s : Set (UnitLogPerfection Ω)) :
    @IsOpen _ (algebraicUnitPerfectionIndTopologyAbove B) s ↔
      ∀ F : FiniteLocalSubfieldAbove B, @IsOpen _ (unitPerfectionTopology F.val.val)
        (unitPerfectionMap F.val.val.val.toRingHom
          (isometry_intermediateField_inclusion F.val.val) ⁻¹' s) := by
  rw [algebraicUnitPerfectionIndTopologyAbove, isOpen_iSup_iff]
  rfl

theorem algebraicUnitPerfectionIndTopologyAbove_eq (B : FiniteLocalSubfield p Ω) :
    algebraicUnitPerfectionIndTopologyAbove B =
      algebraicUnitPerfectionIndTopology (Ω := Ω) (p := p) := by
  apply TopologicalSpace.ext
  funext s
  apply propext
  rw [isOpen_algebraicUnitPerfectionIndTopologyAbove_iff,
    isOpen_algebraicUnitPerfectionIndTopology_iff]
  constructor
  · intro hs F
    obtain ⟨H, hFH⟩ := finiteLocalSubfieldAbove_cofinal B F
    letI := unitPerfectionTopology F.val
    letI := unitPerfectionTopology H.val.val
    have hp := (hs H).preimage (continuous_unitPerfectionMap
      (finiteLocalSubfieldInclusion hFH) (isometry_finiteLocalSubfieldInclusion hFH))
    convert hp using 1
    ext x
    simp only [Set.mem_preimage]
    rw [unitPerfectionMap_comp]
    rfl
  · intro hs F
    exact hs F.val

end

end LeanFormal.IUT.LocalFieldLogarithm
