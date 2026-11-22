/- U-R C2 consumer adapter (kurt): lambda-weight theta/P5 interface.

Re-exports the paper-weight theta readout and H_pkt weight for consumers
(Mzk1URC2AssemblyActual / C2ThetaInput): theta := ksThetaHullLogRoot_lam,
w := thetaLamWeight (paper lambda/d_mod).  No new objects, no conditions.

Default heartbeats (heartbeat-cleanup batch).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaAdapterActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- paper theta_P5 readout with the paper lambda/d_mod weight family. -/
noncomputable abbrev paperThetaHullLogRoot_lam : ℝ := ksThetaHullLogRoot_lam (l := l) T

/-- paper H_pkt weight lambda_v/d_mod. -/
noncomputable abbrev paperHpktWeight (b : Bad (nativePlaceSelection T)) : ℝ :=
  thetaLamWeight T b

/-- paper H_pkt weighted packet hull with the paper weights. -/
noncomputable abbrev paperHpkt (packetV : Bad (nativePlaceSelection T) → ℝ) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
    (thetaLamWeight T) packetV

/-- theta_P5 <= H_pkt in the paper lambda-weight family. -/
theorem paperThetaHullLogRoot_le_Hpkt
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ packetV b) :
    paperThetaHullLogRoot_lam (l := l) T ≤ paperHpkt (l := l) T packetV :=
  ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam (l := l) T packetV hperB

#print axioms paperThetaHullLogRoot_le_Hpkt

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaAdapterActual
end