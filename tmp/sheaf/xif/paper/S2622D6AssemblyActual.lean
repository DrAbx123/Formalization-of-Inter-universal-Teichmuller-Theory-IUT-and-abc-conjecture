import tmp.sheaf.xif.paper.S2577CoverIsoAssemblyActual
import tmp.sheaf.xif.paper.S2620D6HFWActual
import tmp.sheaf.xif.paper.S2621D6HBKActual
import tmp.sheaf.xif.paper.S2586C0BridgeActual

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
open LeanFormal.IUT.XiFPaper.S2620D6HFWActual
open LeanFormal.IUT.XiFPaper.S2621D6HBKActual
open LeanFormal.IUT.XiFPaper.S2586C0BridgeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2622D6AssemblyActual

/-- D6 canonical cover isomorphism from the independent forward/backward halves. -/
theorem S2622CanonicalCoverIsoFromData :
    S2562CanonicalCoverIsoFromData := by
  intro X S hS D
  revert X hS D
  intro X hS D
  cases X with
  | mk source map finiteEtale =>
    cases hS
    refine ⟨?_⟩
    convert S2577CoverIso S map finiteEtale D
      (S2620_hfw (S := S) (map := map) (finiteEtale := finiteEtale) (D := D))
      (S2621_hbk (S := S) (map := map) (finiteEtale := finiteEtale) (D := D)) using 2
    · rw [S2586C0'_eq_C0]
      rfl
    · rfl
    · rfl
    · rfl

end LeanFormal.IUT.XiFPaper.S2622D6AssemblyActual
end