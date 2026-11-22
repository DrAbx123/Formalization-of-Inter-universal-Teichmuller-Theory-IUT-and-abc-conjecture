import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
# Weak concrete Kummer log action

Instead of proving a full group action equality with the log-Kummer layer, this
file proves the weak actual log-quantity statement needed for a direct
inequality: the concrete qUnit power action on the Theta completion image has
log norm equal to (power + theta exponent) times the actual qUnit log norm.

The qUnit is the actual concrete C3 q unit (ConcreteC3DonorActual).  The Theta
completion image is concreteQUnit^(gauss exponent) from
ConcreteCompletionImageToLiteralIQActual.  No full SourceTimesMuKummerLayer
identification, no multiradial action and no inequality are asserted.

No empty type, no True/PUnit/axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.WeakConcreteKummerLogActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual Theta-pilot image index: processions times signed labels. -/
abbrev ThetaPilotImageIndex : Type :=
  ThetaPilotCarrier l × SignedLabel l.value

/-- The actual theta exponent attached to a signed label. -/
def thetaImageExponent (idx : ThetaPilotImageIndex (l := l)) : Nat :=
  (gaussExponent idx.2.1).toNat

/-- The actual concrete qUnit at the supplied finite place. -/
noncomputable def weakQUnit :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ :=
  candidateUnits (K := I.initial.arithmetic.Fmod) place
    (Classical.choice (finitePlaceQCandidate_nonempty place.val))

/-- The actual concrete Theta completion image. -/
noncomputable def weakThetaImage
    (idx : ThetaPilotImageIndex (l := l)) :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ :=
  weakQUnit I place ^ thetaImageExponent (l := l) idx

/-- The actual qUnit log norm. -/
noncomputable def concreteQUnitLogNorm : Real :=
  Real.log ‖(weakQUnit I place :
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)‖

/-- The actual qUnit power action on the completion unit group. -/
noncomputable def concreteQUnitPowerAction
    (m : Nat)
    (u : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ) :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ :=
  weakQUnit I place ^ m * u

/-- The actual log quantity of the qUnit power action. -/
noncomputable def concreteQUnitPowerLogAction (m : Nat) : Real :=
  (m : Real) * concreteQUnitLogNorm I place

/-- The qUnit power action log is the power times the qUnit log norm. -/
theorem concreteQUnitPowerAction_log
    (m : Nat)
    (u : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ) :
    Real.log ‖(concreteQUnitPowerAction I place m u :
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)‖ =
      concreteQUnitPowerLogAction I place m +
        Real.log ‖(u : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)‖ := by
  unfold concreteQUnitPowerAction concreteQUnitPowerLogAction concreteQUnitLogNorm
  rw [Units.val_mul, norm_mul,
    Real.log_mul
      (norm_ne_zero_iff.mpr (Units.ne_zero (weakQUnit I place ^ m)))
      (norm_ne_zero_iff.mpr (Units.ne_zero u))]
  rw [Units.val_pow_eq_pow_val, norm_pow, Real.log_pow]

/-- The actual Theta completion image log quantity. -/
theorem concreteThetaImage_log
    (idx : ThetaPilotImageIndex (l := l)) :
    Real.log ‖(weakThetaImage I place idx :
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)‖ =
      (thetaImageExponent (l := l) idx : Real) *
        concreteQUnitLogNorm I place := by
  unfold weakThetaImage concreteQUnitLogNorm
  rw [Units.val_pow_eq_pow_val, norm_pow, Real.log_pow]

/-- Weak log effect of the qUnit power action on the Theta completion image. -/
theorem concreteThetaImage_action_log
    (m : Nat) (idx : ThetaPilotImageIndex (l := l)) :
    Real.log ‖(concreteQUnitPowerAction I place m
        (weakThetaImage I place idx) :
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)‖ =
      concreteQUnitPowerLogAction I place m +
        (thetaImageExponent (l := l) idx : Real) *
          concreteQUnitLogNorm I place := by
  rw [concreteQUnitPowerAction_log, concreteThetaImage_log]

/-- The weak log quantity is additive in the power. -/
theorem concreteQUnitPowerLogAction_add (m n : Nat) :
    concreteQUnitPowerLogAction I place (m + n) =
      concreteQUnitPowerLogAction I place m +
        concreteQUnitPowerLogAction I place n := by
  unfold concreteQUnitPowerLogAction
  push_cast
  ring

/-- The qUnit itself is the 1-power action value. -/
theorem concreteQUnitPowerAction_one
    (u : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ) :
    concreteQUnitPowerAction I place 1 u = weakQUnit I place * u := by
  simp [concreteQUnitPowerAction]

end LeanFormal.IUT.XiFPaper.WeakConcreteKummerLogActual
