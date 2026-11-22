/- H1a coordinate decomposition, routed through the generic integralRing
coordinate theorem in Node09H1aGenericCoordinateActual. -/
import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aProductFormulaActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual

variable {J : Type*} [Fintype J] [DecidableEq J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, IsUltrametricDist (E j)]
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))

/-- The j-th coordinate submodule, via the generic construction. -/
noncomputable def coordSubmodule (M : Submodule (integralRing hna) ((j : J) → E j))
    (j : J) : Submodule (Integers (E j)) (E j) :=
  Node09H1aGenericCoordinateActual.coordSubmodule hna M j

/-- An integralRing-submodule of a product is the product of its coordinate
projections (generic H1a theorem). -/
theorem submodule_eq_pi_coord (M : Submodule (integralRing hna) ((j : J) → E j)) :
    (M : Set ((j : J) → E j)) =
      Set.pi Set.univ (fun j => (coordSubmodule hna M j : Set (E j))) :=
  Node09H1aGenericCoordinateActual.submodule_eq_pi_coord hna M

#check coordSubmodule
#check submodule_eq_pi_coord
end LeanFormal.IUT.XiFPaper.Node09H1aProductFormulaActual
end
