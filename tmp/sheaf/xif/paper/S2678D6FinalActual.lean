import tmp.sheaf.xif.paper.S2620D6HFWActual
import tmp.sheaf.xif.paper.S2621D6HBKActual
import tmp.sheaf.xif.paper.S2586C0BridgeActual
import tmp.sheaf.xif.paper.S2577CoverIsoAssemblyActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
open LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S2577CoverIsoAssemblyActual
open LeanFormal.IUT.XiFPaper.S2584IsoRelationsActual
open LeanFormal.IUT.XiFPaper.S2586C0BridgeActual
open LeanFormal.IUT.XiFPaper.S2620D6HFWActual
open LeanFormal.IUT.XiFPaper.S2621D6HBKActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2678D6FinalActual

/-- Forward half transported from C0' to C0 using S2586C0'_eq_C0. -/
theorem S2678_hfw_C0
    (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S1728CoverMapRel
      (S1641CoverMapComp
        (S2573CoverMap S map finiteEtale D)
        (S2574CoverMapBack S map finiteEtale D))
      (S1641CoverMapId (S2517InvObj (S2573C0 S map finiteEtale D))) := by
  rw [← S2586C0'_eq_C0]
  exact S2620_hfw S map finiteEtale D

theorem S2678CanonicalCoverIsoFromData :
    S2562CanonicalCoverIsoFromData := by
  intro X S hS D
  revert X hS D
  intro X hS D
  cases X with
  | mk source map finiteEtale =>
    cases hS
    refine ⟨?_⟩
    rw [← S2586C0'_eq_C0]
    exact S2577CoverIso S map finiteEtale D
      (S2678_hfw_C0 S map finiteEtale D)
      (S2621_hbk S map finiteEtale D)

#check S2678_hfw_C0
#check S2678CanonicalCoverIsoFromData
#print axioms S2678_hfw_C0
#print axioms S2678CanonicalCoverIsoFromData

end LeanFormal.IUT.XiFPaper.S2678D6FinalActual
end