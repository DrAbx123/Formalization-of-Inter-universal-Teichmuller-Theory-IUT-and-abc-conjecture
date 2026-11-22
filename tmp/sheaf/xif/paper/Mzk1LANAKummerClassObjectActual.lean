/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.EtaleTheta.KummerClass

/-!
# Mzk1LANAKummerClassObjectActual — LANA etale theta Kummer-class object

A514: reference object from LANA's actual etale-theta Kummer-class construction
(`Iut.EtaleTheta`, `EtaleTheta/KummerClass.lean`): the theta value `Θ̈(Ü)` as a unit
`etaleThetaUnit t U` and the exact `Z`-action law (EtTh Prop. 1.5(iii))
`Θ̈(s^a Ü) = (-1)^a s^{-a^2} Ü^{-2a} Θ̈(Ü)` in `Kˣ`.

This is the Kummer-class/Ind2-unit data matching O2's `thetaValueMon qroot j`;
the `s^{-a^2}` factor is the same `gaussExp` scaling. No new axiom, no comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAKummerClassObjectActual

open Iut.EtaleTheta
open TateCurvesTheta TateCurvesTheta.TateParameter KummerTheory

variable {K : Type*} [NormedField K] (t : TateParameter K)
variable {s : Kˣ} (hs : s ^ 2 = t.q)

/-- The etale-theta Kummer-class object: theta values as units and their `Z`-action. -/
structure EtaleThetaKummerObject where
  /-- theta value at `s^a * U` as a unit. -/
  thetaUnit : ∀ (a : ℤ) (U : Kˣ), etaleTheta t (s ^ a * U) ≠ 0 → Kˣ
  /-- the unit is the actual etale theta value. -/
  thetaUnit_def : ∀ (a : ℤ) (U : Kˣ) (hU : etaleTheta t (s ^ a * U) ≠ 0),
    thetaUnit a U hU = etaleThetaUnit t (s ^ a * U) hU

/-- The constructed Kummer-class object. -/
noncomputable def etaleThetaKummerObject : EtaleThetaKummerObject t hs where
  thetaUnit a U hU := etaleThetaUnit t (s ^ a * U) hU
  thetaUnit_def _ _ _ := rfl

/-- The `Z`-action law (EtTh Prop. 1.5(iii)):
`Θ̈(s^a Ü) = (-1)^a · s^{-a^2} · Ü^{-2a} · Θ̈(Ü)` as units. -/
theorem etaleThetaKummerObject_action (a : ℤ) (U : Kˣ)
    (hU : etaleTheta t U ≠ 0) :
    (etaleThetaKummerObject t hs).thetaUnit a U
        (etaleTheta_zpow_sqrt_mul_ne_zero t hs a hU) =
      (-1) ^ a * s ^ (-a ^ 2) * U ^ (-2 * a) * etaleThetaUnit t U hU :=
  etaleThetaUnit_zpow_sqrt_mul t hs a U hU

/-- `_constructed`: the Kummer-class object is LANA's `etaleThetaUnit` with the
exact `Z`-action law. -/
theorem etaleThetaKummerObject_constructed (a : ℤ) (U : Kˣ)
    (hU : etaleTheta t U ≠ 0) :
    (etaleThetaKummerObject t hs).thetaUnit a U
        (etaleTheta_zpow_sqrt_mul_ne_zero t hs a hU) =
      etaleThetaUnit t (s ^ a * U) (etaleTheta_zpow_sqrt_mul_ne_zero t hs a hU) :=
  rfl

#check etaleThetaKummerObject_action
#check etaleThetaKummerObject_constructed

end LeanFormal.IUT.XiFPaper.Mzk1LANAKummerClassObjectActual
end
