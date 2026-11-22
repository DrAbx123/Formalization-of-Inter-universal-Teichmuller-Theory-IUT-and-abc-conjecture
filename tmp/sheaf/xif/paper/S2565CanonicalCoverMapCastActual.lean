import tmp.sheaf.xif.paper.S2564CanonicalCoverMapLevelActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2565CanonicalCoverMapCastActual

theorem S2565Cast_S1742
    {S S' : Iut.SchemeOverField F} (h : S = S') (f : S ⟶ S2482AffineOver) :
    (congrArg S1742YS h) ▸ S1742StrongTransOfHom f
      = S1742StrongTransOfHom (h ▸ f) := by
  cases h
  rfl

#check S2565Cast_S1742
#print axioms S2565Cast_S1742
end LeanFormal.IUT.XiFPaper.S2565CanonicalCoverMapCastActual
end