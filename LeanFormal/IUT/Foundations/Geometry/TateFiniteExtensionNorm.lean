import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# The spectral norm on a finite extension

The constructions in this file use the existing field and algebra structures on
the extension. The norm is constructed from `spectralNorm`, rather than supplied
as an assumption. Completeness uses finite dimensionality over the complete base.
-/

namespace IUT.TateFiniteExtensionNorm

variable (K E : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [Field E] [Algebra K E] [FiniteDimensional K E]

/-- The spectral norm gives the given finite extension a normed field structure. -/
noncomputable abbrev extensionNormedField : NormedField E :=
  spectralNorm.normedField K E

/-- The constructed normed field retains the original field operations. -/
theorem extensionNormedField_toField :
    (extensionNormedField K E).toField = (inferInstance : Field E) := rfl

/-- The constructed norm is the spectral norm itself. -/
theorem extension_norm_eq_spectralNorm (x : E) :
    letI := extensionNormedField K E
    ‖x‖ = spectralNorm K E x := by
  rfl

/-- Restriction along the given algebra map recovers the base norm exactly. -/
theorem extension_norm_algebraMap (a : K) :
    letI := extensionNormedField K E
    ‖algebraMap K E a‖ = ‖a‖ := by
  exact spectralNorm_extends a

/-- The constructed norm is multiplicative. -/
theorem extension_norm_mul (x y : E) :
    letI := extensionNormedField K E
    ‖x * y‖ = ‖x‖ * ‖y‖ := by
  letI := extensionNormedField K E
  exact norm_mul x y

/-- The constructed norm satisfies the ultrametric inequality. -/
theorem extension_norm_add_le_max (x y : E) :
    letI := extensionNormedField K E
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  exact isNonarchimedean_spectralNorm (K := K) (L := E) x y

/-- The spectral norm gives an ultrametric distance. -/
theorem extension_isUltrametricDist :
    letI := extensionNormedField K E
    IsUltrametricDist E := by
  letI := extensionNormedField K E
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := E))

/-- The given scalar action is compatible with the constructed norm. -/
noncomputable abbrev extensionNormedSpace :
    letI := extensionNormedField K E
    NormedSpace K E := by
  exact spectralNorm.normedSpace K E

/-- The given algebra structure is compatible with the constructed norm. -/
noncomputable abbrev extensionNormedAlgebra :
    letI := extensionNormedField K E
    NormedAlgebra K E := by
  exact spectralNorm.normedAlgebra K E

/-- The constructed normed scalar structure retains the original scalar action. -/
theorem extensionNormedSpace_toModule :
    letI := extensionNormedField K E
    (extensionNormedSpace K E).toModule = (inferInstance : Module K E) := by
  rfl

/-- The constructed normed algebra retains the given algebra structure. -/
theorem extensionNormedAlgebra_toAlgebra :
    letI := extensionNormedField K E
    (extensionNormedAlgebra K E).toAlgebra = (inferInstance : Algebra K E) := by
  rfl

/-- Finite dimensionality over the complete base gives completeness. -/
theorem extension_completeSpace :
    letI := extensionNormedField K E
    CompleteSpace E := by
  exact spectralNorm.completeSpace K E

/-- The original scalar multiplication satisfies the exact norm identity. -/
theorem extension_norm_smul (a : K) (x : E) :
    letI := extensionNormedField K E
    ‖a • x‖ = ‖a‖ * ‖x‖ := by
  letI := extensionNormedField K E
  letI := extensionNormedSpace K E
  exact norm_smul a x

/-- An actual multiplicative ultrametric norm extending the base norm exists.

The topology in this statement is induced by the explicitly constructed spectral
normed field. The scalar and algebra structures in the conclusion are proved to
retain the given structures; they are not assumptions of the theorem.
-/
theorem exists_complete_ultrametric_norm_extension :
    letI := extensionNormedField K E
    ∃ extensionNorm : E → ℝ,
      (∀ x, extensionNorm x = ‖x‖) ∧
      (∀ a : K, extensionNorm (algebraMap K E a) = ‖a‖) ∧
      (∀ x y, extensionNorm (x * y) = extensionNorm x * extensionNorm y) ∧
      (∀ x y, extensionNorm (x + y) ≤ max (extensionNorm x) (extensionNorm y)) ∧
      (∀ (a : K) (x : E), extensionNorm (a • x) = ‖a‖ * extensionNorm x) ∧
      IsUltrametricDist E ∧ CompleteSpace E ∧
      (∃ compatibleScalars : NormedSpace K E,
        compatibleScalars.toModule = (inferInstance : Module K E)) ∧
      (∃ compatibleAlgebra : NormedAlgebra K E,
        compatibleAlgebra.toAlgebra = (inferInstance : Algebra K E)) := by
  letI := extensionNormedField K E
  exact ⟨spectralNorm K E, fun _ => rfl, extension_norm_algebraMap K E,
    extension_norm_mul K E, extension_norm_add_le_max K E, extension_norm_smul K E,
    extension_isUltrametricDist K E, extension_completeSpace K E,
    ⟨extensionNormedSpace K E, extensionNormedSpace_toModule K E⟩,
    ⟨extensionNormedAlgebra K E, extensionNormedAlgebra_toAlgebra K E⟩⟩

end IUT.TateFiniteExtensionNorm
