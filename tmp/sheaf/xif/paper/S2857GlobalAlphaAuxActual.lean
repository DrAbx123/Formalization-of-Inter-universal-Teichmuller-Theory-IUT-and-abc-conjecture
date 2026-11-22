import tmp.sheaf.xif.paper.S2857GlobalAlphaActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2857GlobalAlphaAuxActual

variable (K : Type) [Field K] [DecidableEq K]

theorem hOverlap_fac :
    ∃ h : pullback ((D K).ι (ULift.up true : (D K).J)) ((D K).ι (ULift.up false : (D K).J)) ⟶
        (D K).V ((ULift.up true : (D K).J), (ULift.up false : (D K).J)),
      h ≫ (D K).f (ULift.up true : (D K).J) (ULift.up false : (D K).J) =
        pullback.fst ((D K).ι (ULift.up true : (D K).J)) ((D K).ι (ULift.up false : (D K).J)) := by
  classical
  let i : (D K).J := ULift.up true
  let j : (D K).J := ULift.up false
  let ht := (D K).vPullbackConeIsLimit i j
  let hOverlap := PullbackCone.IsLimit.lift ht
    (pullback.fst ((D K).ι i) ((D K).ι j))
    (pullback.snd ((D K).ι i) ((D K).ι j))
    (pullback.condition)
  refine ⟨hOverlap, ?_⟩
  exact PullbackCone.IsLimit.lift_fst ht
    (pullback.fst ((D K).ι i) ((D K).ι j))
    (pullback.snd ((D K).ι i) ((D K).ι j)) (pullback.condition)

#check hOverlap_fac
#print axioms hOverlap_fac

end LeanFormal.IUT.XiFPaper.S2857GlobalAlphaAuxActual
end
