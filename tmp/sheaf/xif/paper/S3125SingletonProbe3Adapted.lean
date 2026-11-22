import tmp.sheaf.xif.paper.EtaleCoverQuotientCategoryActual
open LeanFormal.IUT.XiFPaper.EtaleCoverQuotientCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open Iut CategoryTheory
noncomputable section
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable (A B : OrbicurveFiniteEtaleCover X)
variable (f g : OrbicurveFiniteEtaleCoverMap A B)
example (e : f.map ≅ g.map) : f.map = g.map := by
  exact?
