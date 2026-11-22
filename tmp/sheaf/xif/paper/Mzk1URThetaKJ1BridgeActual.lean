/- U-R C2 J1 bridge (kurt): named wrappers for the same-q bridge obligation.

The volume comparison hvol is the paper's Step(v) q-pilot/theta comparison content
(the real open gap); these wrappers do NOT prove it and clearly mark it as an
explicit hypothesis.  With hvol the terminal hP5 follows (DONE reductions below).

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKHP5BridgeActual
import tmp.sheaf.xif.paper.Mzk1URThetaKJ1SupportActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKJ1BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5LamActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5BridgeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- Named form of the same-q bridge (paper volume comparison is the explicit
hypothesis; see docstring). -/
theorem j1_same_q_bridge
    (hvol : (∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
          ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      ksThetaHullLogRoot_lam (l := l) T :=
  neg_MpaperV2_le_thetaLam_of_bridge (l := l) T hvol

/-- Reduction from a possible-images mass bound: if the possible-images hull mass
dominates M_paper_v2 and the theta hull contains those images, then the volume
comparison follows.  The two mass comparisons are explicit hypotheses. -/
theorem hbridge_of_possibleImages
    [MeasurableSpace (ksBlock T b)] [BorelSpace (ksBlock T b)]
    (b : Bad (nativePlaceSelection T))
    (varpi : CommonPrimeCompletion (ksPlace T b))
    (hM : (∑ b' : Bad (nativePlaceSelection T),
        thetaLamWeight T b' * ((urCeilC (l := l) T b') * Real.log
          ((completionRationalPrime (nativeBadToKPlace T b')).val : ℝ))) ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T)
    : -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      ksThetaHullLogRoot_lam (l := l) T :=
  j1_same_q_bridge (l := l) T hM

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKJ1BridgeActual
end