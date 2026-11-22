import tmp.sheaf.xif.paper.S2076GeneralLiftAPIGapActual

/-! # S2077: component Iso of a strong-transformation iso

Implements the first missing API of S2076: for a general cone `c` and a test
object `U`, the component of `c.commutes` is an iso
`(c.toA.vcomp f.map).app U ≅ (c.toB.vcomp g.map).app U`.  The proof extracts
the component of `c.commutes.hom_inv_id` using the modification component
formulas, so no `IsIso` instance is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2077ComponentIsoActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual

universe u

variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- The component of `c.commutes` at a test object, as an iso of functors. -/
noncomputable def S2077ComponentIso (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Iso ((c.toA.vcomp f.map).app U) ((c.toB.vcomp g.map).app U) where
  hom := c.commutes.hom.as.app U
  inv := c.commutes.inv.as.app U
  hom_inv_id := by
    have h := congrArg (fun m => m.as.app U) c.commutes.hom_inv_id
    simpa only [Pseudofunctor.StrongTrans.homCategory, CategoryStruct.comp,
      CategoryStruct.id, Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Pseudofunctor.StrongTrans.Modification.id_app] using h
  inv_hom_id := by
    have h := congrArg (fun m => m.as.app U) c.commutes.inv_hom_id
    simpa only [Pseudofunctor.StrongTrans.homCategory, CategoryStruct.comp,
      CategoryStruct.id, Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Pseudofunctor.StrongTrans.Modification.id_app] using h

#print axioms S2077ComponentIso

end LeanFormal.IUT.XiFPaper.S2077ComponentIsoActual

end
