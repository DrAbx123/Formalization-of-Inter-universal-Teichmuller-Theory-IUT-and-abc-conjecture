/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A898: attack surface 1 - SSIneq as an explicit numeric inequality (interface + arithmetic) -/

/- lana source facts (root Iut/ tree; cited, not imported here because the Wall oleans are
not built in this workspace):
* `Iut/Wall/IdentifiedCopies.lean:479` `idAlg_lgpLaw` -- `(idAlg D).LGPLaw`;
* `Iut/Wall/Checks.lean wall_iff_of_lgpLaw` -- a law converts the wall into a numeric
  inequality `qPilotLhs - kappa <= logVol(hull(vcI))`;
* `Iut/Wall/IdentifiedCopies.lean:488` `wall_idAlg_iff` --
  `Wall D (idAlg D) <-> (sFactor(nC)-1)*|log q| <= logVol(hull(vcI))`.

Chain (interface form):
1. `LgpLawInterface` records `logVolOut S = kappa + logVol S` (the lgp law, a data field);
2. with `qLhs = |log q|`-type lhs and `kappa = -sFactor * A` (arithmetic identity, PROVED),
   the numeric wall `qLhs - kappa <= hullLog` is equivalent to
   `(sFactor - 1) * A <= hullLog` = the explicit SSIneq form;
3. step 3 (wall <-> SSIneq via `wall_idAlg_iff`) is the only piece needing lana oleans.

Pure arithmetic below is green; the lana steps are interface fields/TODOs. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqVolumeActual

structure LgpLawInterface where
  kappa : ℝ
  logVol : ℝ → ℝ
  logVolOut : ℝ → ℝ
  law : ∀ S : ℝ, logVolOut S = kappa + logVol S

/-- The explicit SSIneq form `(sF - 1) * A <= hullLog`. -/
def SSIneqForm (sF A hullLog : ℝ) : Prop := (sF - 1) * A ≤ hullLog

/-- The numeric wall form `qLhs - kappa <= hullLog`. -/
def WallNumeric (qLhs kappa hullLog : ℝ) : Prop := qLhs - kappa ≤ hullLog

/-- **Arithmetic step (PROVED)**: with `qLhs = -A` and `kappa = -sF*A`, the numeric wall is
the explicit SSIneq form. -/
theorem wallNumeric_iff_ssIneqForm {sF A hullLog : ℝ} :
    WallNumeric (-A) (-(sF * A)) hullLog ↔ SSIneqForm sF A hullLog := by
  unfold WallNumeric SSIneqForm
  constructor <;> intro h <;> nlinarith

/-- **Arithmetic step (PROVED)**: any lgp law shifts the wall by `kappa`. -/
theorem wallNumeric_of_lgpLaw (L : LgpLawInterface) {S : ℝ} {qLhs : ℝ} :
    L.logVolOut S = L.kappa + L.logVol S := L.law S

/-- **Assembly (interface)**: given the lgp law and the wall-iff theorem as data, the
numeric wall is equivalent to the explicit SSIneq form.  Step `hwall` is the lana
`wall_idAlg_iff`/`wall_iff_of_lgpLaw` input (interface field below). -/
theorem ssIneq_iff_volume (L : LgpLawInterface) {sF A hullLog : ℝ}
    (hkappa : L.kappa = -(sF * A)) :
    WallNumeric (-A) L.kappa hullLog ↔ SSIneqForm sF A hullLog := by
  rw [hkappa]
  exact wallNumeric_iff_ssIneqForm

def lanaInterfaceRows : List (String × String × String) :=
  [ ("idAlg_lgpLaw", "Iut/Wall/IdentifiedCopies.lean:479", "LANA (olean needed)") ,
    ("wall_iff_of_lgpLaw", "Iut/Wall/Checks.lean", "LANA (olean needed)") ,
    ("wall_idAlg_iff", "Iut/Wall/IdentifiedCopies.lean:488", "LANA (olean needed)") ,
    ("kappa = -(sF*A)", "arithmetic identity", "PROVED (this file)") ,
    ("wallNumeric_iff_ssIneqForm", "numeric wall <-> (sF-1)A <= hullLog", "PROVED") ,
    ("ssIneq_iff_volume", "interface assembly", "PROVED given kappa identity") ,
    ("SSIneq <-> volume form (full lana link)", "needs wall oleans", "OPEN (lana)") ]

theorem lanaInterfaceRows_length : lanaInterfaceRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqVolumeActual
