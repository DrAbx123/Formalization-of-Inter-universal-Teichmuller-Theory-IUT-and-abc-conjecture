import tmp.sheaf.xif.paper.S2584IsoRelationsActual
import tmp.sheaf.xif.paper.S2566CanonicalMapTransportActual
import tmp.sheaf.xif.paper.S2568CanonicalCoverCommutesActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2566CanonicalMapTransportActual
open LeanFormal.IUT.XiFPaper.S2568CanonicalCoverCommutesActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
open LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2586C0BridgeActual

variable {S : Iut.SchemeOverField S2480QiActual.F}
variable {map : (S2517TStack S).Hom S2482Orbicurve.stack}
variable {finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map}
variable {D : S2554CanonicalData (X0 S map finiteEtale) S rfl}

theorem S2586C0'_eq_C0 :
    S2573C0' S map finiteEtale D = S2573C0 S map finiteEtale D := by
  unfold S2573C0' S2573C0 S2554CanonicalCover
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  let h := S2573hsch S map finiteEtale D
  have hcanon := S2566CanonicalMap_eq (X0 S map finiteEtale) S
    (S2573S' S map finiteEtale D) rfl (S2573hS' S map finiteEtale D) h
  apply CategoryTheory.CostructuredArrow.obj_ext
  · exact S2568eqToHom_comp_canonical_transport (X0 S map finiteEtale) S
      (S2573S' S map finiteEtale D) rfl (S2573hS' S map finiteEtale D) h

#print axioms S2586C0'_eq_C0

end LeanFormal.IUT.XiFPaper.S2586C0BridgeActual
end
