/-
# U-R C2 theta side: the weighted monotone-sum interface (Lead split (A))

This file contains exactly two theorems (both proved, three axioms):

* thetaHullLog_le_ucHpkt: with the actual weights gamma_b = nativeBadLocalWeight
  (the same weight family as in actualThetaHullLogRoot, nonnegative by
  actualTargetWeight_nonneg) and per-b theta-hull log at most the per-b packet
  value, the actual weighted theta hull log is at most the weighted packet hull
  sum_b gamma_b * packetV b = ucWeightedHpkt (nativeBadLocalWeight T) packetV;
* thetaHullLog_le_ulHpkt: the same against Mzk1ULHpktActual.Hpkt, which is the
  left side of the U-L hpaper reduction.

The per-b input hperB (actualLocalHullLog b <= packetV b) is NOT proved here; it
is exactly the missing root-extension-to-tensor transport (U-R lane, kurt): the
root-hull scaling formulas are conditional on a 2l-th root of q which does not
exist in the completion (S342QVFamilyRootImpossibleActual).  No sign argument
(H_pkt >= 0) is used.
-/

import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.Mzk1UCHpktActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

/-- Weighted monotone sum (theta <= H_pkt).  With the actual weights
gamma_b = nativeBadLocalWeight (the same family as in actualThetaHullLogRoot) and
per-b theta hull log at most the per-b packet value, the actual weighted theta hull
log is at most the weighted packet hull sum_b gamma_b V_b.  This is exactly the
htheta input of uc_c3_paperConstants / uc_c4. -/
theorem thetaHullLog_le_ucHpkt
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b, actualLocalHullLog (l := l) T b ≤ packetV b) :
    actualThetaHullLogRoot (l := l) T ≤
      ucWeightedHpkt (nativeBadLocalWeight T) packetV := by
  unfold actualThetaHullLogRoot ucWeightedHpkt
  exact Finset.sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (hperB b) (actualTargetWeight_nonneg (l := l) T b)

/-- The same weighted bound against the U-L Hpkt of Mzk1ULHpktActual, which is the
left side consumed by the U-L hpaper reduction. -/
theorem thetaHullLog_le_ulHpkt
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b, actualLocalHullLog (l := l) T b ≤ packetV b) :
    actualThetaHullLogRoot (l := l) T ≤
      Mzk1ULHpktActual.Hpkt (nativeBadLocalWeight T) packetV := by
  rw [← Mzk1UCHpktActual.ucWeightedHpkt_eq_ulHpkt]
  exact thetaHullLog_le_ucHpkt (l := l) T packetV hperB

#print axioms thetaHullLog_le_ucHpkt
#print axioms thetaHullLog_le_ulHpkt

end LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2
end