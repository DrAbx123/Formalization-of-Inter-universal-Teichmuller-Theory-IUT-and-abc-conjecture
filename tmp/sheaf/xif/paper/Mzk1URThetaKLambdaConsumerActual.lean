/- U-R C2 theta lambda consumer (kurt): squeeze + URC2 hP5 shapes for david.

Re-exports the lambda squeeze and the terminal hP5 reduction in consumer form.
Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLambdaSqueezeActual
import tmp.sheaf.xif.paper.Mzk1URThetaKHP5BridgeActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5LamActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaAdapterActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaSqueezeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- URC2 hP5 field shape in the lambda-weight family. -/
theorem urc2_hP5_lambda
    (hbridge : LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      ∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
          ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) :
    LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      ksThetaHullLogRoot_lam (l := l) T :=
  hbridge.trans (ksThetaHullLogRoot_lam_lower (l := l) T)

/-- URC2 theta/H_pkt pair (lambda weights) for the C2 assembly. -/
theorem urc2_theta_pair_lambda
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ packetV b) :
    ksThetaHullLogRoot_lam (l := l) T ≤ paperHpkt (l := l) T packetV :=
  paperThetaHullLogRoot_le_Hpkt (l := l) T packetV hperB


/-- C2 form in the lambda-weight family: q_P5 <= H_pkt from the bridge and per-b bounds. -/
theorem urc2_c2_lambda
    (hbridge : LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      ∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
          ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)))
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ packetV b) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T ≤
      paperHpkt (l := l) T packetV :=
  (neg_le_neg hbridge).trans
    ((ksThetaHullLogRoot_lam_lower (l := l) T).trans
      (paperThetaHullLogRoot_le_Hpkt (l := l) T packetV hperB))

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaConsumerActual
end