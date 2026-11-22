import tmp.sheaf.xif.paper.EtaleCoverQuotientCategoryActual
open LeanFormal.IUT.XiFPaper.EtaleCoverQuotientCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open Iut CategoryTheory
noncomputable section
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
example : S3125SingletonClassesTarget (F := F) (X := X) := by
  intro A B f g h
  rcases h with ⟨e⟩
  -- e : f.map ≅ g.map
  have hm : f.map = g.map := by
    exact Subsingleton.elim _ _
