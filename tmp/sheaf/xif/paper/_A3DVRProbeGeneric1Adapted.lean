import Mathlib

noncomputable section
open Polynomial
open scoped TensorProduct
namespace A3DVRProbe

universe u

variable {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B] [FaithfulSMul A B]

local notation "BK" => Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))

example (r : B) (hr : r ∈ nonZeroDivisors B) : IsUnit (algebraMap B BK r) := by
  haveI : Algebra.Etale (FractionRing A) BK := by
    have e : FractionRing A ⊗[A] B ≃ₐ[FractionRing A] BK :=
      Localization.tensorRightAlgEquiv (nonZeroDivisors A) B
    exact Algebra.Etale.of_equiv e
  haveI : IsArtinianRing BK := IsArtinianRing.of_finite (FractionRing A) BK
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    (IsLocalization.map_nonZeroDivisors_le (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) BK
      (Set.mem_image_of_mem (algebraMap B BK) hr))

end A3DVRProbe
