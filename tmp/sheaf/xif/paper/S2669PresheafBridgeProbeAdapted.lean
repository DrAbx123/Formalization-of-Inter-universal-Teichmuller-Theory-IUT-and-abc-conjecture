import tmp.sheaf.xif.paper.S2668FiberCoherenceActual
import tmp.sheaf.xif.paper.S2665TorsorSheafActual
import tmp.sheaf.xif.paper.S2668D9ReductionActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2669PresheafBridgeProbeAdapted

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
open LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
open LeanFormal.IUT.XiFPaper.S2665TorsorSheafActual
open LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]
variable (D : S2622TorsorData (l := l) (F := F))

example (S : Iut.SchemeOverField F)
    (M N : (S2668FiberPseudofunctor D.toS2619ActionGroupoidData).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    (S2668FiberPseudofunctor D.toS2619ActionGroupoidData).presheafHom M N =
      S2620TorsorPresheaf D.toS2619ActionGroupoidData S M.back N.back := by
  letI : MulAction (S2619G l) (S2619Hom (l := l) (F := F) D.toS2619ActionGroupoidData (Opposite.op S)) :=
    S2619MulAction (l := l) (F := F) (D := D.toS2619ActionGroupoidData)
  rfl

end LeanFormal.IUT.XiFPaper.S2669PresheafBridgeProbeAdapted
end
