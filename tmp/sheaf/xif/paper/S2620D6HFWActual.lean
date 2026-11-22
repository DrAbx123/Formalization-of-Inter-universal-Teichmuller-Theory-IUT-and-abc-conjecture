import tmp.sheaf.xif.paper.S2577CoverIsoAssemblyActual
import tmp.sheaf.xif.paper.S2583CastIso2Actual
import tmp.sheaf.xif.paper.S2575CoverIsoActual

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
open LeanFormal.IUT.XiFPaper.S2567CanonicalDataTransportActual
open LeanFormal.IUT.XiFPaper.S2568CanonicalCoverCommutesActual
open LeanFormal.IUT.XiFPaper.S2569CoverMapActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
open LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S2577CoverIsoAssemblyActual
open LeanFormal.IUT.XiFPaper.S2583CastIso2Actual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2620D6HFWActual

/-- Forward half of the D6 cover isomorphism, independent of Kummer. -/
theorem S2620_hfw
    (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S1728CoverMapRel
      (S1641CoverMapComp
        (S2573CoverMap S map finiteEtale D)
        (S2574CoverMapBack S map finiteEtale D))
      (S1641CoverMapId (S2517InvObj (S2573C0' S map finiteEtale D))) := by
  simpa [S1728CoverMapRel, S2575B, S2517InvObj, S2517TStack_scheme_fiber] using S2575_fwd_iso S map finiteEtale D

end LeanFormal.IUT.XiFPaper.S2620D6HFWActual
end