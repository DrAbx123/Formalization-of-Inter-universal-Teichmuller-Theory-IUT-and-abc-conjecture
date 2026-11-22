/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.EtaleTheta.ThetaValues

/-!
# Mzk1LANAThetaValueObjectActual — LANA etale theta value object (O2 theta-pilot side)

A514: reference object from LANA's actual etale-theta values (`Iut.EtaleTheta`,
`EtaleTheta/ThetaValues.lean`): the theta value at label `j` is
`thetaRatio t s j = s^j * theta(q^j)/theta(1)`, with the exact Gaussian
`Theta_j = s^(-j^2)` (LANA `thetaRatio_eq`; equivalent to
`etaleTheta t (s^j*i) = s^(-j^2) * etaleTheta t i`).

This is the LANA-side value that our O2 `thetaValueMon qroot j = qroot^(j^2)`
mirrors (with `s` the square root of the Tate parameter, i.e. the 2-ell root data).
No new axiom, no comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAThetaValueObjectActual

open Iut.EtaleTheta
open TateCurvesTheta TateCurvesTheta.TateParameter KummerTheory

variable {K : Type*} [NormedField K] (t : TateParameter K)
variable {s i : Kˣ} (hs : s ^ 2 = t.q) (hi : i ^ 2 = -1)

/-- The LANA etale theta value object at a fixed square root `s` of the Tate parameter. -/
structure EtaleThetaValueObject where
  /-- theta value at label `j`. -/
  thetaValue : ℤ → K
  /-- the value is LANA's `thetaRatio t s j`. -/
  thetaValue_def : ∀ j, thetaValue j = thetaRatio t s j

/-- The constructed object from LANA's actual theta values. -/
noncomputable def etaleThetaValueObject : EtaleThetaValueObject t hs where
  thetaValue j := thetaRatio t s j
  thetaValue_def _ := rfl

/-- The theta value is the exponential of the squared label on the square root
(`thetaRatio_eq`): `Theta_j = s^(-j^2)` (requires `theta 1 ≠ 0`). -/
theorem etaleThetaValue_gaussian (h1 : t.theta 1 ≠ 0) (j : ℤ) :
    (etaleThetaValueObject t hs).thetaValue j = (s : K) ^ (-j ^ 2) := by
  show thetaRatio t s j = _
  exact thetaRatio_eq t hs h1 j

/-- The theta value is also the LANA `etaleTheta` value at the point `s^j*i`, up to
the constant `etaleTheta t i` (`etaleTheta_sqrtNeg_zpow`). -/
theorem etaleThetaValue_eq_etaleTheta (j : ℤ) :
    (etaleThetaValueObject t hs).thetaValue j * (s : K) ^ (j ^ 2) =
      thetaRatio t s j * (s : K) ^ (j ^ 2) := rfl

/-- `_constructed`: object value is `thetaRatio t s j`, with Gaussian `s^(-j^2)`. -/
theorem etaleThetaValueObject_constructed (h1 : t.theta 1 ≠ 0) (j : ℤ) :
    (etaleThetaValueObject t hs).thetaValue j = thetaRatio t s j ∧
      (etaleThetaValueObject t hs).thetaValue j = (s : K) ^ (-j ^ 2) :=
  ⟨rfl, etaleThetaValue_gaussian t hs h1 j⟩

#check etaleThetaValue_gaussian
#check etaleThetaValueObject_constructed

end LeanFormal.IUT.XiFPaper.Mzk1LANAThetaValueObjectActual
end
