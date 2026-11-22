import tmp.sheaf.xif.paper.S3135HaarPushforwardActual

/-!
# task-56 wiring append: trivial pushforward identities for the uniqueness route

**COMPONENT, not a paper object.**  Consumer: F4 (b1) `S3135AdditiveHaarModulusLaw`.

Records the base cases of the pushforward family used by the Haar-uniqueness route:
the identity scaling gives back the actual Haar measure, and the companion pushforward
along the inverse scaling composes back to the identity measure.  These are the
bookkeeping facts needed when the uniqueness equation
`S3135HaarUniquenessScalarStep` is proved via
`integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport` + `Measure.ext`.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135HaarPushforwardActual

namespace LeanFormal.IUT.XiFPaper.S3135HaarUniquenessWiringActual

local instance measCSF6 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF6 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- The identity scaling gives back the actual Haar measure. -/
theorem s3135_pushforward_one :
    sourceHullHaar.map (fun x => (1 : concreteLogShellField) * x) = sourceHullHaar := by
  simp

/-- The pushforward along the inverse scaling composes with the pushforward along the
scaling to the identity measure (elementary map bookkeeping for the uniqueness
route). -/
theorem s3135_pushforward_inv_comp (c : concreteLogShellField) (hc : c ≠ 0) :
    (sourceHullHaar.map (fun x => c * x)).map (fun x => c⁻¹ * x) = sourceHullHaar := by
  rw [Measure.map_map]
  · have hfun : (fun x => c⁻¹ * x) ∘ (fun x => c * x) =
        (fun x : concreteLogShellField => x) := by
      funext x
      show c⁻¹ * (c * x) = x
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [hfun]
    exact Measure.map_id
  · exact (continuous_const.mul continuous_id).measurable
  · exact (continuous_const.mul continuous_id).measurable

#check s3135_pushforward_one
#check s3135_pushforward_inv_comp

end LeanFormal.IUT.XiFPaper.S3135HaarUniquenessWiringActual
end
