import tmp.sheaf.xif.paper.EtaleCoverCategoryActual
open LeanFormal.IUT.XiFPaper.EtaleCoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open Iut CategoryTheory
noncomputable section
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
example : Category (OrbicurveFiniteEtaleCover X) where
  toCategoryStruct := S3124CoverCategoryStruct
  id_comp := by
    intro A B f
    change S1641CoverMapComp (S1641CoverMapId A) f = f
    rfl
