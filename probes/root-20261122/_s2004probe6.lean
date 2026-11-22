
import tmp.sheaf.xif.paper.S1998IsoCommaPrestackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option pp.all false
set_option pp.proofs false

namespace TestNS
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ := LocallyDiscrete.mk (Opposite.op S)

example {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}} (α : Pseudofunctor.StrongTrans F G)
    {X : Site} {a : ↑(F.obj (U X))} :
    (α.app (U X)).toFunctor.map (𝟙 a) = 𝟙 ((α.app (U X)).toFunctor.obj a) := by
  rw [CategoryTheory.Functor.map_id]

example {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}} (α : Pseudofunctor.StrongTrans F G)
    {X : Site} {a : ↑(F.obj (U X))} {b : ↑(G.obj (U X))} (f : (α.app (U X)).toFunctor.obj a ⟶ b) :
    (α.app (U X)).toFunctor.map (𝟙 a) ≫ f = f := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

example {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}} (α : Pseudofunctor.StrongTrans F G)
    {X : Site} {a : ↑(F.obj (U X))} :
    𝟙 ((α.app (U X)).toFunctor.obj a) ≫ (α.app (U X)).toFunctor.map (𝟙 a) = 𝟙 _ := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

end TestNS
