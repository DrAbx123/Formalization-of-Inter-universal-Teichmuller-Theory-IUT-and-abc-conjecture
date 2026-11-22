import tmp.sheaf.xif.paper.S3135HaarPushforwardActual

/-!
# task-56 bookkeeping: bijection cancellation for the uniqueness route

**COMPONENT, not a paper object.**  Consumer: F4 (b1) `S3135HaarUniquenessScalarStep`.

Elementary set bookkeeping needed when the scalar step is assembled from
`Measure.map`-form pushforwards: applying multiplication by `c` and then by
`c⁻¹` (or conversely) to a set returns the set, so the actual Haar mass is
preserved.  These are the cancellation facts used when combining the pushforward
along `c` with the companion pushforward along `c⁻¹` in the uniqueness equation.
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

namespace LeanFormal.IUT.XiFPaper.S3135HaarImageCancellationActual

local instance measCSF7 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF7 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- Multiplication by `c` followed by `c⁻¹` returns the set (bijection
cancellation). -/
theorem s3135_mul_inv_image_eq (c : concreteLogShellField) (hc : c ≠ 0)
    (S : Set concreteLogShellField) :
    (fun x => c * x) '' ((fun x => c⁻¹ * x) '' S) = S := by
  rw [Set.image_image]
  have hfun : (fun x => c * (c⁻¹ * x)) = (fun x : concreteLogShellField => x) := by
    funext x
    show c * (c⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [hfun]
  exact Set.image_id S

/-- The actual Haar mass is invariant under the pair of mutually inverse scalings. -/
theorem s3135_haar_image_cancel (c : concreteLogShellField) (hc : c ≠ 0)
    (S : Set concreteLogShellField) :
    sourceHullHaar ((fun x => c * x) '' ((fun x => c⁻¹ * x) '' S)) =
      sourceHullHaar S := by
  rw [s3135_mul_inv_image_eq c hc S]

#check s3135_mul_inv_image_eq
#check s3135_haar_image_cancel

end LeanFormal.IUT.XiFPaper.S3135HaarImageCancellationActual
end
