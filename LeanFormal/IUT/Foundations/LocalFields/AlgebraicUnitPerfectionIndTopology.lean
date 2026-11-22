import LeanFormal.IUT.Foundations.LocalFields.UnitPerfectionFunctoriality
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Finite-subfield ind topologies and the actual logarithm

Both topologies are final topologies of actual finite local-field layers.
On the source the layer maps are the canonical localizations of the
original unit maps. The logarithm identifies the two final topologies.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]

abbrev FiniteLocalSubfield (p : ℕ) [Fact p.Prime] (Ω : Type*)
    [NormedField Ω] [NormedAlgebra ℚ_[p] Ω] :=
  { F : IntermediateField ℚ_[p] Ω // FiniteDimensional ℚ_[p] F }

instance finiteLocalSubfieldFiniteDimensional (F : FiniteLocalSubfield p Ω) :
    FiniteDimensional ℚ_[p] F.val := F.property

instance finiteLocalSubfieldProperSpace (F : FiniteLocalSubfield p Ω) : ProperSpace F.val :=
  FiniteDimensional.proper ℚ_[p] F.val

omit [IsUltrametricDist Ω] in
theorem finiteLocalSubfields_directed (F G : FiniteLocalSubfield p Ω) :
    ∃ H : FiniteLocalSubfield p Ω, F.val ≤ H.val ∧ G.val ≤ H.val := by
  exact ⟨⟨F.val ⊔ G.val, IntermediateField.finiteDimensional_sup _ _⟩,
    le_sup_left, le_sup_right⟩

abbrev algebraicFieldIndTopology : TopologicalSpace Ω :=
  ⨆ F : FiniteLocalSubfield p Ω,
    TopologicalSpace.coinduced F.val.val.toRingHom inferInstance

abbrev algebraicUnitPerfectionIndTopology : TopologicalSpace (UnitLogPerfection Ω) :=
  ⨆ F : FiniteLocalSubfield p Ω, TopologicalSpace.coinduced
    (unitPerfectionMap F.val.val.toRingHom (isometry_intermediateField_inclusion F.val))
    (unitPerfectionTopology F.val)

omit [IsUltrametricDist Ω] in
theorem isOpen_algebraicFieldIndTopology_iff (s : Set Ω) :
    @IsOpen _ (algebraicFieldIndTopology (Ω := Ω) (p := p)) s ↔
      ∀ F : FiniteLocalSubfield p Ω, IsOpen (F.val.val.toRingHom ⁻¹' s) := by
  rw [algebraicFieldIndTopology, isOpen_iSup_iff]
  rfl

theorem isOpen_algebraicUnitPerfectionIndTopology_iff (s : Set (UnitLogPerfection Ω)) :
    @IsOpen _ (algebraicUnitPerfectionIndTopology (Ω := Ω) (p := p)) s ↔
      ∀ F : FiniteLocalSubfield p Ω, @IsOpen _ (unitPerfectionTopology F.val)
        (unitPerfectionMap F.val.val.toRingHom
          (isometry_intermediateField_inclusion F.val) ⁻¹' s) := by
  rw [algebraicUnitPerfectionIndTopology, isOpen_iSup_iff]
  rfl

variable [CharZero Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

omit [IsUltrametricDist Ω] [CharZero Ω] in
theorem exists_finiteLocalSubfield_preimage (x : Ω) :
    ∃ F : FiniteLocalSubfield p Ω, ∃ y : F.val, F.val.val.toRingHom y = x :=
  ⟨⟨finiteElementField (p := p) x, inferInstance⟩, finiteElementLift (p := p) x, rfl⟩

theorem finiteLocalSubfieldPerfectionMap_injective (F : FiniteLocalSubfield p Ω) :
    Function.Injective (unitPerfectionMap F.val.val.toRingHom
      (isometry_intermediateField_inclusion F.val)) := by
  intro x y hxy
  apply (unitLogPerfectionEquiv (K := F.val) (p := p)).injective
  apply F.val.val.injective
  rw [← unitPerfectionMap_log_commute (p := p) F.val.val.toRingHom
      (isometry_intermediateField_inclusion F.val) x,
    ← unitPerfectionMap_log_commute (p := p) F.val.val.toRingHom
      (isometry_intermediateField_inclusion F.val) y, hxy]

theorem exists_finiteLocalSubfieldPerfection_preimage (x : UnitLogPerfection Ω) :
    ∃ F : FiniteLocalSubfield p Ω, ∃ y : UnitLogPerfection F.val,
      unitPerfectionMap F.val.val.toRingHom (isometry_intermediateField_inclusion F.val) y = x := by
  obtain ⟨F, y, hy⟩ := exists_finiteLocalSubfield_preimage (p := p)
    (algebraicUnitPerfectionEquiv (p := p) x)
  refine ⟨F, (unitLogPerfectionEquiv (K := F.val) (p := p)).symm y, ?_⟩
  apply (algebraicUnitPerfectionEquiv (p := p)).injective
  rw [unitPerfectionMap_log_commute (p := p), LinearEquiv.apply_symm_apply, hy]

def algebraicUnitPerfectionIndHomeomorph :
    letI := algebraicUnitPerfectionIndTopology (Ω := Ω) (p := p)
    letI := algebraicFieldIndTopology (Ω := Ω) (p := p)
    UnitLogPerfection Ω ≃ₜ Ω := by
  letI := algebraicUnitPerfectionIndTopology (Ω := Ω) (p := p)
  letI := algebraicFieldIndTopology (Ω := Ω) (p := p)
  refine { (algebraicUnitPerfectionEquiv (Ω := Ω) (p := p)).toEquiv with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_def.mpr
    intro s hs
    apply (isOpen_algebraicUnitPerfectionIndTopology_iff _).mpr
    intro F
    letI : TopologicalSpace F.val :=
      (inferInstance : PseudoMetricSpace F.val).toUniformSpace.toTopologicalSpace
    letI := unitPerfectionTopology F.val
    have hsF := (isOpen_algebraicFieldIndTopology_iff (p := p) s).mp hs F
    have hlocal := hsF.preimage
      (unitLogPerfectionHomeomorph (K := F.val) (p := p)).continuous
    change IsOpen ((fun x : UnitLogPerfection F.val =>
      algebraicUnitPerfectionEquiv (p := p)
        (unitPerfectionMap F.val.val.toRingHom
          (isometry_intermediateField_inclusion F.val) x)) ⁻¹' s)
    convert hlocal using 1
    ext x
    simp only [Set.mem_preimage]
    rw [unitPerfectionMap_log_commute (p := p)]
    rfl
  · apply continuous_def.mpr
    intro s hs
    apply (isOpen_algebraicFieldIndTopology_iff (p := p) _).mpr
    intro F
    letI : TopologicalSpace F.val :=
      (inferInstance : PseudoMetricSpace F.val).toUniformSpace.toTopologicalSpace
    letI := unitPerfectionTopology F.val
    have hsF := (isOpen_algebraicUnitPerfectionIndTopology_iff (p := p) s).mp hs F
    have hlocal := hsF.preimage
      (unitLogPerfectionHomeomorph (K := F.val) (p := p)).symm.continuous
    change IsOpen ((fun y : F.val =>
      (algebraicUnitPerfectionEquiv (p := p)).symm (F.val.val.toRingHom y)) ⁻¹' s)
    convert hlocal using 1
    ext y
    change (algebraicUnitPerfectionEquiv (p := p)).symm (F.val.val.toRingHom y) ∈ s ↔
      unitPerfectionMap F.val.val.toRingHom (isometry_intermediateField_inclusion F.val)
        ((unitLogPerfectionEquiv (p := p)).symm y) ∈ s
    have hvalue := unitPerfectionMap_log_commute (p := p) F.val.val.toRingHom
      (isometry_intermediateField_inclusion F.val)
      ((unitLogPerfectionEquiv (K := F.val) (p := p)).symm y)
    rw [LinearEquiv.apply_symm_apply] at hvalue
    rw [← hvalue, LinearEquiv.symm_apply_apply]

end

end LeanFormal.IUT.LocalFieldLogarithm
