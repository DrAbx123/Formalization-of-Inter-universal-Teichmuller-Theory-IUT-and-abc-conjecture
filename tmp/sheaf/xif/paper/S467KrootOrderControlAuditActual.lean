import tmp.sheaf.xif.paper.S459KrootCandidateActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual

-- S467 audit: from order_K = e * order_F and gcd(order_F,l)=1, one
-- CANNOT conclude (2l) | order_K.  The arithmetic counterexample e=m=1
-- shows the missing ramification/2-torsion controls are essential.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S467KrootOrderControlAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S459KrootCandidateActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def qVFamilyKRamificationIdx : Nat :=
  ((nativeBadLift T).lift b).maximalIdeal.asIdeal.ramificationIdx'
    (qVFamilyKLift T b).maximalIdeal.asIdeal

theorem qVFamilyK_order_factorization :
    (qVFamilyK T b).order =
      qVFamilyKRamificationIdx T b * (qVFamily T b).order :=
  qVFamilyK_order T b

theorem qVFamily_order_coprime_l :
    Nat.Coprime (qVFamily T b).order l.value :=
  qVFamily_order_coprime T b

-- The abstract implication is false even with m coprime to l.
theorem not_uniform_twoL_dvd_factorization :
    ¬ (∀ e m : Nat, Nat.Coprime m l.value → (2 * l.value) ∣ e * m) := by
  intro h
  have hd : (2 * l.value) ∣ (1 : Nat) * 1 :=
    h 1 1 (Nat.coprime_one_left l.value)
  have hone : 2 * l.value = 1 := Nat.dvd_one.mp (by simpa using hd)
  have hge : 5 ≤ l.value := l.ge_five
  omega

-- Exact necessary conditions under the actual factorization.
theorem twoL_dvd_order_K_requires_ramification :
    (2 * l.value) ∣ (qVFamilyK T b).order →
      l.value ∣ qVFamilyKRamificationIdx T b := by
  intro h
  have hcop : Nat.Coprime (qVFamily T b).order l.value :=
    qVFamily_order_coprime T b
  have hK : (qVFamilyK T b).order =
      qVFamilyKRamificationIdx T b * (qVFamily T b).order :=
    qVFamilyK_order_factorization T b
  have hdiv : (2 * l.value) ∣
      qVFamilyKRamificationIdx T b * (qVFamily T b).order := by
    simpa [hK] using h
  have hdivl : l.value ∣
      qVFamilyKRamificationIdx T b * (qVFamily T b).order :=
    dvd_trans (by exact ⟨2, by ring⟩) hdiv
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdivl
structure KrootOrderControlGap where
  l_dvd_ramification : l.value ∣ qVFamilyKRamificationIdx T b
  two_dvd_order_K : 2 ∣ (qVFamilyK T b).order
  root_valuation_control : Prop
  root_stack_control : Prop

def KrootOrderControlGapRequired : Prop :=
  Nonempty (KrootOrderControlGap T b)

#check qVFamilyKRamificationIdx
#check qVFamilyK_order_factorization
#check not_uniform_twoL_dvd_factorization
#check twoL_dvd_order_K_requires_ramification
#check KrootOrderControlGap

end LeanFormal.IUT.XiFPaper.S467KrootOrderControlAuditActual

end