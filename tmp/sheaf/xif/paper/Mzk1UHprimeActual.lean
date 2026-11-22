import tmp.sheaf.xif.paper.Mzk1UCHpktActual
import tmp.sheaf.xif.paper.Mzk1UCEtaPrmActual
import Mathlib.Tactic
/-!
# hprime at david's `etaPrm` witness

`Mzk1UCHpktActual.hprime_paperConstants` (david, line 191) already proves
`paperLstarLogs eMod l ≤ (4/3) paperEar eMod l eta_prm` from the Section2 threshold witness
and the two-branch prime count.  This file is the thin instantiation at david's actual
`etaPrm` (`Mzk1UCEtaPrmActual.etaPrm`), for kurt's C3-upper.  No duplicate proof.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1UHprimeActual
open LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual

/-- `l*_mod log(s≤) ≤ (4/3) E_ar` at the actual `etaPrm`. -/
theorem hprime_paperLstarLogs_le {eMod : Nat} (he : 1 ≤ eMod) {l : ℝ} (hl : 1 ≤ l) :
    paperLstarLogs eMod l ≤ (4 / 3) * paperEar eMod l etaPrm :=
  Mzk1UCHpktActual.hprime_paperConstants etaPrm_pos
    (fun η h => primeCounting_le_four_thirds h) he hl le_rfl

#print axioms hprime_paperLstarLogs_le
end LeanFormal.IUT.XiFPaper.Mzk1UHprimeActual
end