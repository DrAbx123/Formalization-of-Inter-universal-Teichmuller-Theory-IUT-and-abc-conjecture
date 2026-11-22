import tmp.sheaf.xif.paper.S2856HfOverlapActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import tmp.sheaf.xif.paper.S2821E37ProjectiveOverActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual

variable (K : Type) [Field K] [DecidableEq K]

noncomputable abbrev D := E37ProjGlueData K (S2820E37TransitionIso K)

noncomputable def globalAlphaComp (i : ULift.{0} Bool) :
    (D K).openCover.X i ⟶ S2820E37ProjectiveScheme K :=
  match i with
  | ⟨false⟩ => S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K
  | ⟨true⟩ => chartYNegGlued K

noncomputable def globalAlpha
    (h : ∀ x y, pullback.fst ((D K).openCover.f x) ((D K).openCover.f y) ≫
        globalAlphaComp K x =
      pullback.snd ((D K).openCover.f x) ((D K).openCover.f y) ≫
        globalAlphaComp K y) :
    S2820E37ProjectiveScheme K ⟶ S2820E37ProjectiveScheme K :=
  (D K).openCover.glueMorphisms (globalAlphaComp K) h

#check globalAlphaComp
#check globalAlpha

end LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
end
