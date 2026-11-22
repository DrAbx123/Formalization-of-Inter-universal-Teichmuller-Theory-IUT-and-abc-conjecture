import tmp.sheaf.xif.paper.S2523ActionDataActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2524CorrectedGroupAssembly

universe u

open LeanFormal.IUT.XiFPaper.S2519CoverBaseActual
open LeanFormal.IUT.XiFPaper.S2520GaloisCoreActual
open LeanFormal.IUT.XiFPaper.S2521CoverMorphismsActual
open LeanFormal.IUT.XiFPaper.S2522FiberDataActual
open LeanFormal.IUT.XiFPaper.S2523ActionDataActual

structure OrbicurveEtaleFundamentalGroupCorrected
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F)
    (group : ProfiniteGrp.{u}) where
  coverBase : CoverBase X
  galoisCore : GaloisCore X coverBase.coverCategory
  coverMorphisms : CoverMorphisms X coverBase.coverCategory
  fiberData :
    FiberData X coverBase.coverCategory galoisCore.galoisCategory
      coverBase.baseScheme coverBase.basePoint
  actionData :
    ActionData X coverBase.coverCategory galoisCore.galoisCategory
      fiberData.fiber fiberData.fiberFunctor group

def assembly
    {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
    {group : ProfiniteGrp.{u}}
    (B : CoverBase X)
    (G : GaloisCore X B.coverCategory)
    (M : CoverMorphisms X B.coverCategory)
    (D : FiberData X B.coverCategory G.galoisCategory
      B.baseScheme B.basePoint)
    (A : ActionData X B.coverCategory G.galoisCategory
      D.fiber D.fiberFunctor group) :
    OrbicurveEtaleFundamentalGroupCorrected X group where
  coverBase := B
  galoisCore := G
  coverMorphisms := M
  fiberData := D
  actionData := A

#check OrbicurveEtaleFundamentalGroupCorrected
#check assembly
end LeanFormal.IUT.XiFPaper.S2524CorrectedGroupAssembly
end