import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitPerfectionIndTopology

/-!
# Cofinality of finite local subfields containing a fixed base field

The compositum with a fixed finite Qp subfield is again finite. Thus the
ind topology can be computed using only finite fields containing that
base, as in the fixed-field description of IUT III Proposition 3.1.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {Ω : Type*} [NormedField Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]

abbrev FiniteLocalSubfieldAbove (B : FiniteLocalSubfield p Ω) :=
  { F : FiniteLocalSubfield p Ω // B.val ≤ F.val }

theorem finiteLocalSubfieldAbove_cofinal (B F : FiniteLocalSubfield p Ω) :
    ∃ H : FiniteLocalSubfieldAbove B, F.val ≤ H.val.val := by
  obtain ⟨H, hBH, hFH⟩ := finiteLocalSubfields_directed B F
  exact ⟨⟨H, hBH⟩, hFH⟩

def finiteLocalSubfieldInclusion {F G : FiniteLocalSubfield p Ω} (h : F.val ≤ G.val) :
    F.val →+* G.val := (IntermediateField.inclusion h).toRingHom

theorem isometry_finiteLocalSubfieldInclusion {F G : FiniteLocalSubfield p Ω}
    (h : F.val ≤ G.val) : Isometry (finiteLocalSubfieldInclusion h) :=
  Isometry.of_dist_eq (fun _ _ => rfl)

abbrev algebraicFieldIndTopologyAbove (B : FiniteLocalSubfield p Ω) : TopologicalSpace Ω :=
  ⨆ F : FiniteLocalSubfieldAbove B,
    TopologicalSpace.coinduced F.val.val.val.toRingHom inferInstance

theorem isOpen_algebraicFieldIndTopologyAbove_iff (B : FiniteLocalSubfield p Ω) (s : Set Ω) :
    @IsOpen _ (algebraicFieldIndTopologyAbove B) s ↔
      ∀ F : FiniteLocalSubfieldAbove B, IsOpen (F.val.val.val.toRingHom ⁻¹' s) := by
  rw [algebraicFieldIndTopologyAbove, isOpen_iSup_iff]
  rfl

theorem algebraicFieldIndTopologyAbove_eq (B : FiniteLocalSubfield p Ω) :
    algebraicFieldIndTopologyAbove B = algebraicFieldIndTopology (Ω := Ω) (p := p) := by
  apply TopologicalSpace.ext
  funext s
  apply propext
  rw [isOpen_algebraicFieldIndTopologyAbove_iff, isOpen_algebraicFieldIndTopology_iff]
  constructor
  · intro hs F
    obtain ⟨H, hFH⟩ := finiteLocalSubfieldAbove_cofinal B F
    exact (hs H).preimage (isometry_finiteLocalSubfieldInclusion hFH).continuous
  · intro hs F
    exact hs F.val

end

end LeanFormal.IUT.LocalFieldLogarithm
