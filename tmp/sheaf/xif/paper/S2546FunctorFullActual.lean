import tmp.sheaf.xif.paper._FullD3D4Agent
import tmp.sheaf.xif.paper.S2543CorrectedQuotMapActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2543CorrectedQuotMapActual
open LeanFormal.IUT.XiFPaper.FullD3D4Agent
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2546FunctorFullActual

/-- Unconditional Full of the corrected algebra-side functor. -/
theorem S2546FunctorFull : S2540Functor.Full where
  map_surjective := by
    intro A B g
    obtain ⟨f, hf⟩ := S2543QuotMapRSurjective_holds
      (A := B.unop) (B := A.unop) g
    refine ⟨Quiver.Hom.op f, ?_⟩
    exact hf

#check S2546FunctorFull
#print axioms S2546FunctorFull

end LeanFormal.IUT.XiFPaper.S2546FunctorFullActual
end
