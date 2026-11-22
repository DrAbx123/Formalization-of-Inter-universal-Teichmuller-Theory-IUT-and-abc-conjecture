/- H1a max-norm direct proof: the product integral ring is characterized
coordinatewise by the sup norm condition, and the idempotent coordinate
scalars are integral.  Direct max-norm route, independent of min valuation. -/
import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual
import tmp.sheaf.xif.paper.Node09H1aProductFormulaActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMaxNormDirectActual

open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, IsUltrametricDist (E j)]
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))

/-- Coordinatewise sup-norm unit condition. -/
def maxNormLeOne (x : (j : J) → E j) : Prop := ∀ j, ‖x j‖ ≤ 1

/-- The actual integral ring is exactly the coordinatewise sup-norm unit
region.  This is the direct max-norm membership characterization. -/
theorem mem_integralRing_iff_maxNorm (x : (j : J) → E j) :
    x ∈ integralRing hna ↔ maxNormLeOne (E := E) x :=
  Iff.rfl

/-- The idempotent coordinate scalar is integral (max-norm route). -/
theorem singleO_mem_integralRing (j : J) (a : Integers (E j)) :
    singleO hna j a ∈ integralRing hna :=
  (singleO hna j a).property

/-- H1a coordinate decomposition, with the max-norm direct membership. -/
theorem submodule_eq_pi_coord_maxNorm
    (M : Submodule (integralRing hna) ((j : J) → E j)) :
    (M : Set ((j : J) → E j)) =
      Set.pi Set.univ (fun j =>
        (coordSubmodule hna M j : Set (E j))) :=
  submodule_eq_pi_coord hna M

#check mem_integralRing_iff_maxNorm
#check singleO_mem_integralRing
#check submodule_eq_pi_coord_maxNorm

end LeanFormal.IUT.XiFPaper.Node09H1aMaxNormDirectActual
end
