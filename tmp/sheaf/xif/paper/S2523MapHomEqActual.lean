import tmp.sheaf.xif.paper.S2522ForwardWellDefinedConditional
import tmp.sheaf.xif.paper.S1896BoundaryCuspActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivMapActual
open LeanFormal.IUT.XiFPaper.S2522ForwardWellDefinedConditional
open LeanFormal.IUT.XiFPaper.S2519ForwardFunctorPartialActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2523MapHomEqActual

theorem S2523MapHomEq : S2522MissingMapHomEq := by
  intro C D φ ψ hrel
  let bcC := C.finiteEtale.baseChange S2482AffineOver S2517Point
  let bcD := D.finiteEtale.baseChange S2482AffineOver S2517Point
  let e := Classical.choice hrel
  let m : (S2517Square D).ConeMorphism (S2517Cone φ) (S2517Cone ψ) := {
    toX := by
      let Bicat := Iut.EtaleStackPseudofunctor F
      letI : Bicategory Bicat := inferInstance
      exact (@Bicategory.whiskerLeftIso Bicat _ (S2517YS bcC.pullbackScheme) C.source.fiber D.source.fiber bcC.toSource φ.map ψ.map e).hom
    toY := 𝟙 _,
    compatibility := by
      apply S1896Modification_subsingleton (S := S2482AffineOver)
  }
  let m' : (S2517Square D).ConeMorphism (S2517Cone ψ) (S2517Cone φ) := {
    toX := by
      let Bicat := Iut.EtaleStackPseudofunctor F
      letI : Bicategory Bicat := inferInstance
      exact (@Bicategory.whiskerLeftIso Bicat _ (S2517YS bcC.pullbackScheme) C.source.fiber D.source.fiber bcC.toSource ψ.map φ.map e.symm).hom
    toY := 𝟙 _,
    compatibility := by
      apply S1896Modification_subsingleton (S := S2482AffineOver)
  }
  let liftφ := (S2517Witness D).lift _ (S2517Cone φ)
  let liftψ := (S2517Witness D).lift _ (S2517Cone ψ)
  let hom : liftφ ⟶ liftψ := (S2517Witness D).liftTwoCell _ (S2517Cone φ) (S2517Cone ψ) m
  let inv : liftψ ⟶ liftφ := (S2517Witness D).liftTwoCell _ (S2517Cone ψ) (S2517Cone φ) m'
  let eLift : liftφ ≅ liftψ := {
    hom := hom,
    inv := inv,
    hom_inv_id := S1896Modification_subsingleton (S := bcD.pullbackScheme) _ _,
    inv_hom_id := S1896Modification_subsingleton (S := bcD.pullbackScheme) _ _
  }
  exact S1742HomOfStrongTrans_congr eLift

theorem S2523ForwardMapWellDefined : S2519ForwardMapWellDefined :=
  S2522WellDefined_of_mapHomEq S2523MapHomEq

#check S2523ForwardMapWellDefined
#print axioms S2523ForwardMapWellDefined
#print axioms S2523MapHomEq
end LeanFormal.IUT.XiFPaper.S2523MapHomEqActual
end