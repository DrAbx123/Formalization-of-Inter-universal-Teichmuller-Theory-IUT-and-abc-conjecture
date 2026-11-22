/- U-R C2 theta lambda squeeze (kurt): lower bound and H_pkt upper bound in the
paper lambda/d_mod weight family, for consumers of URC2Data/C4.

  -(sum_b thetaLamWeight_b * (urCeilC_b * log p_b)) <= ksThetaHullLogRoot_lam <= Hpkt.

No new objects, no conditions; this file only recombines DONE inequalities.

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC registry: kurt-adapters-20261117 (1M heartbeats; Lead-approved list).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKHP5LamActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaSqueezeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5LamActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- Lambda-weighted theta squeeze: lower volume bound and H_pkt upper bound. -/
theorem ksThetaHullLogRoot_lam_squeeze
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ packetV b) :
    -(∑ b : Bad (nativePlaceSelection T),
      thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      ksThetaHullLogRoot_lam (l := l) T ∧
      ksThetaHullLogRoot_lam (l := l) T ≤
        LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
          (thetaLamWeight T) packetV :=
  ⟨ksThetaHullLogRoot_lam_lower (l := l) T,
    ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam (l := l) T packetV hperB⟩

#print axioms ksThetaHullLogRoot_lam_squeeze


/-- Lambda-weighted theta lower bound (consumer form). -/
theorem theta_lam_lower :
    -(∑ b : Bad (nativePlaceSelection T),
      thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      ksThetaHullLogRoot_lam (l := l) T :=
  ksThetaHullLogRoot_lam_lower (l := l) T

/-- Lambda-weighted theta upper bound by H_pkt (consumer form). -/
theorem theta_lam_upper
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ packetV b) :
    ksThetaHullLogRoot_lam (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (thetaLamWeight T) packetV :=
  ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam (l := l) T packetV hperB

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaSqueezeActual
end