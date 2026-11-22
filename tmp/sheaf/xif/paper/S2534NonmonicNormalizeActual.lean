import tmp.sheaf.xif.paper.S2533NonmonicDedekindActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2534NonmonicNormalizeActual
/-- Explicit-unit normalization: if `u` is a unit with `u = f.leadingCoeff`,
then `C u⁻¹ * f` is monic and `f = C u * (C u⁻¹ * f)`. -/
theorem exists_monic_of_unit_leadingCoeff
    {R : Type*} [CommRing R] (f : R[X]) (u : Rˣ)
    (hu : (u : R) = f.leadingCoeff) :
    ∃ g : R[X], g.Monic ∧ f = C (u : R) * g := by
  refine ⟨C ((u⁻¹ : Rˣ) : R) * f, ?_, ?_⟩
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [← hu]
    simpa using congrArg (fun w : Rˣ => (w : R)) (Units.inv_mul u)
  · rw [← mul_assoc, ← C_mul, Units.mul_inv]
    simp
/-- IsUnit leading coefficient version. -/
theorem exists_monic_of_isUnit_leadingCoeff
    {R : Type*} [CommRing R] (f : R[X]) (hu : IsUnit f.leadingCoeff) :
    ∃ g : R[X], g.Monic ∧ f = C (hu.unit : R) * g :=
  exists_monic_of_unit_leadingCoeff f hu.unit hu.unit_spec
#print axioms exists_monic_of_unit_leadingCoeff
#print axioms exists_monic_of_isUnit_leadingCoeff
end LeanFormal.IUT.XiFPaper.S2534NonmonicNormalizeActual
end
