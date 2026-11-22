/- Route 7.2 structural gap: normed-field/complete instances for the intermediate fields
M of PadicAlgCl p, needed to apply the local-field monogenic results to M. -/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalIFNormedActual

open IntermediateField

variable {p : Nat} [Fact p.Prime]

/-- An intermediate field of PadicAlgCl is a normed field (norm restricted from the closure). -/
instance instNormedField (M : IntermediateField ℚ_[p] (PadicAlgCl p)) : NormedField M :=
  SubfieldClass.toNormedField M

/-- The restriction of the ultrametric to an intermediate field. -/
instance instIsUltrametricDist (M : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsUltrametricDist M :=
  inferInstance

/-- A finite-dimensional intermediate field of PadicAlgCl is complete (over the complete
field Q_p and with the restricted normed-space structure). -/
instance instCompleteSpace (M : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] M] : CompleteSpace M :=
  FiniteDimensional.complete ℚ_[p] M

/-- The restricted normed-algebra structure over Q_p, from the SubalgebraClass instance. -/
instance instNormedAlgebra (M : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    NormedAlgebra ℚ_[p] M :=
  inferInstance

#print axioms instNormedField
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalIFNormedActual
