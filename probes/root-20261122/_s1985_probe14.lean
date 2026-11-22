import tmp.sheaf.xif.paper.S1985SiteLiftNaturalityActual

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace Probe

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

noncomputable def structureMapEq'_test {W : S1728Cover} (c : S1832Bicone f g W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (toB f g) B.map) (structureMap f g) := by
  let eB : @Iso (B.source.fiber ⟶ S1726Orbicurve.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory) (Pseudofunctor.StrongTrans.vcomp g.map C.map) B.map :=
    { hom := g.commutes.hom, inv := g.commutes.inv,
      hom_inv_id := g.commutes.hom_inv_id, inv_hom_id := g.commutes.inv_hom_id }
  let wB : @Iso (sitePseudofunctor f g ⟶ S1726Orbicurve.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory)
      (Pseudofunctor.StrongTrans.vcomp (toB f g) B.map)
      (Pseudofunctor.StrongTrans.vcomp (toB f g) (Pseudofunctor.StrongTrans.vcomp g.map C.map)) :=
    { hom := Bicategory.whiskerLeft (toB f g) eB.inv,
      inv := Bicategory.whiskerLeft (toB f g) eB.hom,
      hom_inv_id := by
        rw [← Bicategory.whiskerLeft_comp, eB.inv_hom_id, Bicategory.whiskerLeft_id]
      inv_hom_id := by
        rw [← Bicategory.whiskerLeft_comp, eB.hom_inv_id, Bicategory.whiskerLeft_id] }
  let aB : @Iso (sitePseudofunctor f g ⟶ S1726Orbicurve.stack.fiber)
      (Pseudofunctor.StrongTrans.homCategory)
      (Pseudofunctor.StrongTrans.vcomp (toB f g) (Pseudofunctor.StrongTrans.vcomp g.map C.map))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (toB f g) g.map) C.map) :=
    (Bicategory.associator (toB f g) g.map C.map).symm
  exact wB.trans aB

end Probe