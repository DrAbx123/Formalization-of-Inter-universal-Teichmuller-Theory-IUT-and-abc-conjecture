import tmp.sheaf.xif.paper.GlobalQPilotProcessionLogVolumeActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.SignedAverageBoundActual

/-! # Global Theta-pilot procession log-volume candidate

IUT III, Theorem 3.11 and Corollary 3.12 (iut3.txt lines 10499-10535,
pp. 173-174): -|log(Theta)| is the procession-normalized mono-analytic
log-volume of the holomorphic hull of the union of possible Theta-pilot images.
The Theta-pilot data are the collection over V_bad of local Theta values
q_v^{j^2}, not a single local q = 1/5 packet.

This file constructs the actual global Theta-pilot procession log-volume
candidate from the actual V_bad base q family:

* baseQReal b = ||(baseQ T b).q|| is the actual real local q_v;
* thetaValueFromQ b j = (baseQReal b) ^ (gaussExponent j).toNat is the actual
  local Theta value for the procession label j;
* localThetaLogVolume b is the actual procession average over j of
  -log thetaValueFromQ b j;
* globalThetaPilotLogVolume is the sum over V_bad.

It proves the exact formula

  globalThetaPilotLogVolume
    = (gaussExponentSum / card(SignedLabel l.value))
      * globalQPilotLogMagnitude.

No fake inequality and no local log(1/5) is used.  The actual holomorphic hull
and possible-image union are not constructed here; this is the actual
q_v/theta-values procession candidate only.  No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual real local q_v: the norm of the base q candidate. -/
noncomputable def baseQReal (b : Bad (nativePlaceSelection T)) : Real :=
  ‖(baseQ T b).q‖

theorem baseQReal_pos (b : Bad (nativePlaceSelection T)) :
    0 < baseQReal T b :=
  norm_pos_iff.mpr (baseQ T b).q_ne_zero

theorem baseQReal_lt_one (b : Bad (nativePlaceSelection T)) :
    baseQReal T b < 1 := by
  have hpos : 0 < -Real.log ‖(baseQ T b).q‖ := baseQLogMagnitude_pos T b
  have hnorm : 0 < ‖(baseQ T b).q‖ := norm_pos_iff.mpr (baseQ T b).q_ne_zero
  have hlog : Real.log ‖(baseQ T b).q‖ < 0 := by linarith
  exact (Real.log_neg_iff hnorm).mp hlog

/-- The actual local Theta value q_v^(j^2) at a bad place. -/
noncomputable def thetaValueFromQ
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : Real :=
  (baseQReal T b) ^ (gaussExponent j.1).toNat

theorem thetaValueFromQ_pos
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    0 < thetaValueFromQ T b j :=
  pow_pos (baseQReal_pos T b) _

theorem log_thetaValueFromQ
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    Real.log (thetaValueFromQ T b j) =
      (gaussExponent j.1).toNat * Real.log (baseQReal T b) := by
  unfold thetaValueFromQ
  rw [Real.log_pow]

/-- The actual base q log-magnitude is minus the log of the actual real q_v. -/
theorem baseQLogMagnitude_eq_neg_log_baseQReal
    (b : Bad (nativePlaceSelection T)) :
    baseQLogMagnitude T b = -Real.log (baseQReal T b) := by
  unfold baseQLogMagnitude baseQReal localLogMagnitude localSignedLog
  rfl

/-- The actual local procession log-volume of the Theta values at b. -/
noncomputable def localThetaLogVolume (b : Bad (nativePlaceSelection T)) : Real :=
  (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
    ∑ j : SignedLabel l.value, -Real.log (thetaValueFromQ T b j)

/-- The actual global Theta-pilot procession log-volume candidate: sum over
V_bad of the local procession log-volumes. -/
noncomputable def globalThetaPilotLogVolume : Real :=
  ∑ b : Bad (nativePlaceSelection T), localThetaLogVolume T b

/-- The local procession log-volume is the Gauss coefficient times the actual
base q log magnitude. -/
theorem localThetaLogVolume_eq :
    localThetaLogVolume T b =
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) *
        baseQLogMagnitude T b := by
  unfold localThetaLogVolume
  have hsum :
      (∑ j : SignedLabel l.value,
        -Real.log (thetaValueFromQ T b j)) =
        (gaussExponentSum (l := l) : Real) *
          (-Real.log (baseQReal T b)) := by
    calc
      (∑ j : SignedLabel l.value,
        -Real.log (thetaValueFromQ T b j)) =
          ∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real) *
              (-Real.log (baseQReal T b)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [log_thetaValueFromQ]
        ring
      _ = (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) *
            (-Real.log (baseQReal T b)) := by
        rw [Finset.sum_mul]
      _ = (gaussExponentSum (l := l) : Real) *
            (-Real.log (baseQReal T b)) := by
        congr 1
        rw [← Nat.cast_sum]
        rfl
  rw [hsum, baseQLogMagnitude_eq_neg_log_baseQReal]
  have hcardnat : 0 < Fintype.card (SignedLabel l.value) := by
    rw [SignedLabel.card_signedLabel]
    exact l.prime.pos
  have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcardnat)
  field_simp [hcard]

/-- The global Theta-pilot procession log-volume is the Gauss coefficient
times the actual global q-pilot log-magnitude. -/
theorem globalThetaPilotLogVolume_eq :
    globalThetaPilotLogVolume T =
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) *
        globalQPilotLogMagnitude T := by
  unfold globalThetaPilotLogVolume
  rw [globalQPilotLogMagnitude_eq_totalLogMagnitude]
  unfold baseQTotalLogMagnitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [localThetaLogVolume_eq]

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual

end
