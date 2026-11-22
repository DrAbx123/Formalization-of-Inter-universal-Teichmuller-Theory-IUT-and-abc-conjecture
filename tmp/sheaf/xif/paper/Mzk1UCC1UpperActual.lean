/-
# U-C C1 upper: weighted paper bound, C3, and C4 from the accepted P5 lower bound

Route section 5.4 (U-C).  The former version of this file specialized C3 under the
toy assumption Hpkt = 0.  Here:

* UC1UpperActual is the actual weighted paper identity B = kappa (A - c_l Q) - M;
* uc_c3_of_weighted_paper turns any actual weighted hull bound Hpkt <= B into C3;
* uc_c4_of_p5 is the route sandwich: P5 lower bound -M <= theta_P5, the reading
  bound theta_P5 <= Hpkt and C3 give C4 = hCor312;
* uc_c4_of_p6_data grounds the lower end in the accepted
  Mzk1P6HThetaNormalization2 (p6_neg_M_le_HTheta2), with M the actual pilot
  magnitude.
-/
import tmp.sheaf.xif.paper.Mzk1UCC3Actual
import tmp.sheaf.xif.paper.P6HThetaNormalization2Actual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1UCC1UpperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual

/-- The actual weighted paper bound of the U-C chain:
B = kappa (A - c_l Q) - M, where B is the weighted average of the packet paper
bounds (U-L packetB) with the actual local-degree weights. -/
def UC1UpperActual (l A Q M B : ℝ) : Prop :=
  B = kappa l * (A - cL l * Q) - M

/-- A weighted packet hull at most the weighted paper bound gives C3. -/
theorem uc_c3_of_weighted_paper {l A Q M Hpkt B : ℝ}
    (hHpkt : Hpkt ≤ B) (hB : UC1UpperActual l A Q M B) :
    Hpkt ≤ kappa l * (A - cL l * Q) - M := by
  unfold UC1UpperActual at hB
  rw [← hB]
  exact hHpkt

/-- C4 = hCor312 from the P5 lower bound -M <= theta_P5, the reading bound
theta_P5 <= H_pkt, and C3.  No Hpkt = 0 assumption. -/
theorem uc_c4_of_p5 {l A Q M theta Hpkt : ℝ} (hkappa : 0 < kappa l)
    (hP5 : -M ≤ theta) (htheta : theta ≤ Hpkt)
    (hC3 : Hpkt ≤ kappa l * (A - cL l * Q) - M) :
    cL l * Q ≤ A :=
  uc_c3_to_c4 hkappa hP5 htheta hC3

/-- C4 with the actual P5 lower bound: -M <= actualThetaHullLogRoot is the accepted
Mzk1P6HThetaNormalization2 (p6_neg_M_le_HTheta2); M is the actual pilot magnitude.
The remaining inputs are exactly the U-R reading bound theta <= H_pkt and the U-C
C3 bound for the actual weighted packet hull. -/
theorem uc_c4_of_p6_data {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    {A Q Hpkt : ℝ} (hkappa : 0 < kappa (l.value : ℝ))
    (htheta : actualThetaHullLogRoot (l := l) T ≤ Hpkt)
    (hC3 : Hpkt ≤ kappa (l.value : ℝ) *
        (A - cL (l.value : ℝ) * Q) - actualQPilotMagnitudeClassical (l := l) T) :
    cL (l.value : ℝ) * Q ≤ A :=
  uc_c4_of_p5 hkappa
    (LeanFormal.IUT.XiFPaper.P6HThetaNormalization2Actual.p6_neg_M_le_HTheta2 (l := l) T)
    htheta hC3

#check UC1UpperActual
#check uc_c3_of_weighted_paper
#check uc_c4_of_p5
#check uc_c4_of_p6_data

end LeanFormal.IUT.XiFPaper.Mzk1UCC1UpperActual
end