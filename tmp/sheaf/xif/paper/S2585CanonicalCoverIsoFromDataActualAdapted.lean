import tmp.sheaf.xif.paper.S2577CoverIsoAssemblyActual
import tmp.sheaf.xif.paper.S2584IsoRelationsActual

noncomputable section
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
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2585CanonicalCoverIsoFromDataActualAdapted

theorem S2585CanonicalCoverIsoFromData :
    S2562CanonicalCoverIsoFromData := by
  intro X S hS D
  revert X hS D
  intro X hS D
  cases X with
  | mk source map finiteEtale =>
    cases hS
    change Nonempty
      (S2517InvObj (S2573C0' S map finiteEtale D) ≅ X0 S map finiteEtale)
    exact ⟨S2577CoverIso S map finiteEtale D
      (S2584_hfw (S := S) (map := map) (finiteEtale := finiteEtale) (D := D))
      (S2584_hbk (S := S) (map := map) (finiteEtale := finiteEtale) (D := D))⟩

#print axioms S2585CanonicalCoverIsoFromData

end LeanFormal.IUT.XiFPaper.S2585CanonicalCoverIsoFromDataActualAdapted
end
