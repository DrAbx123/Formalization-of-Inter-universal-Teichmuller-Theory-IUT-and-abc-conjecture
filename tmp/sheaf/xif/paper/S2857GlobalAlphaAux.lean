import tmp.sheaf.xif.paper.S2857GlobalAlphaActual
import tmp.sheaf.xif.paper.S2856HfOverlapActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2857GlobalAlphaAux

variable (K : Type) [Field K] [DecidableEq K]

noncomputable abbrev D := E37ProjGlueData K (S2820E37TransitionIso K)

noncomputable def hOverlap :
    pullback ((D K).ι (⟨true⟩ : (D K).J)) ((D K).ι (⟨false⟩ : (D K).J)) ⟶
      (D K).V ((⟨true⟩ : (D K).J), (⟨false⟩ : (D K).J)) :=
  PullbackCone.IsLimit.lift
    ((D K).vPullbackConeIsLimit (⟨true⟩ : (D K).J) (⟨false⟩ : (D K).J))
    (pullback.fst ((D K).ι (⟨true⟩ : (D K).J))
      ((D K).ι (⟨false⟩ : (D K).J)))
    (pullback.snd ((D K).ι (⟨true⟩ : (D K).J))
      ((D K).ι (⟨false⟩ : (D K).J)))
    (pullback.condition)

theorem hOverlap_fac :
    hOverlap K ≫ (D K).f (⟨true⟩ : (D K).J) (⟨false⟩ : (D K).J) =
      pullback.fst ((D K).ι (⟨true⟩ : (D K).J))
        ((D K).ι (⟨false⟩ : (D K).J)) := by
  unfold hOverlap
  exact PullbackCone.IsLimit.lift_fst _ _ _ _

#check hOverlap
#check hOverlap_fac

end LeanFormal.IUT.XiFPaper.S2857GlobalAlphaAux
end
