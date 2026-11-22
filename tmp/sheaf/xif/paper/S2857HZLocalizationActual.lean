import tmp.sheaf.xif.paper.S2857GlobalAlphaAuxActual
import tmp.sheaf.xif.paper.S2856HfRingActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaAuxActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2856HfRingActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2857HZLocalizationActual

variable (K : Type) [Field K] [DecidableEq K]

/-- The chart-Y cover piece D(t) is the (true,false) glue-data overlap. -/
theorem chartYCover_f_true_eq_overlap :
    (chartYCover K).f true =
      (D K).f (ULift.up true : (D K).J) (ULift.up false : (D K).J) := by
  rfl

/-- Localized hZ: after localizing at 1+t, the chart-Z endomorphism agrees with
the chart-Z negation transported through alpha. -/
theorem hZ_localization :
    (phiZ K).comp (g1Ring K) =
      (phiZ K).comp ((alpha K).comp (S2853RingHom K)) :=
  hZ K

#check chartYCover_f_true_eq_overlap
#check hZ_localization
#print axioms hZ_localization

end LeanFormal.IUT.XiFPaper.S2857HZLocalizationActual
end
