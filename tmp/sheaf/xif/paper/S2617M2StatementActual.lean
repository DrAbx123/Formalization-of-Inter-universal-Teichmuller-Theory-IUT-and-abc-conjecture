import tmp.sheaf.xif.paper.S2616M2FullWitnessActual
import tmp.sheaf.xif.paper.S2096StackMorphismActual

/-! # S2617: M2 statement actual -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2600M2CommutesActual
open LeanFormal.IUT.XiFPaper.S2616M2FullWitnessActual

namespace LeanFormal.IUT.XiFPaper.S2617M2StatementActual

universe u

noncomputable def baseChangeStatement : S2096BaseChangeStatement := by
  intro X Y m A T s vy Q hs hse hq hqe
  haveI : AlgebraicGeometry.IsFinite Q.projection.left := hq
  haveI : AlgebraicGeometry.Etale Q.projection.left := hqe
  refine ⟨?_, ?_⟩
  · simpa [basePoint] using
      m2Presentation (m := m) (s := s) (vy := vy) (Q := Q)
  · constructor
    · change AlgebraicGeometry.IsFinite
        (Limits.pullback.snd Q.projection.left s.left)
      infer_instance
    · change AlgebraicGeometry.Etale
        (Limits.pullback.snd Q.projection.left s.left)
      infer_instance

#check baseChangeStatement
#print axioms baseChangeStatement

end LeanFormal.IUT.XiFPaper.S2617M2StatementActual
end
