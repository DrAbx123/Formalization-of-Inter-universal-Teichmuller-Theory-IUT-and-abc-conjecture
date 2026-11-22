/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import Mathlib.Tactic

/-! # A849 hull: L5 identification with lana LGP laws (provenance)

lana source `Iut/Wall/IdentifiedCopies.lean` (read-only; olean NOT available):
* `logVol_lgp` (:281): `logVol(LGP·S) = logVol(LGP·O) + logVol(S)`;
* `logVol_lgp_integral` (:444): `logVol(LGP·O) = −sFactor(nC)·absLogQ`;
* `componentVol_scaleElt` (:295): `μ^log(q^{j²}·O) = −j²·ord_p(q)·log p`;
* `idAlg_lgpLaw` (:479), `wall_idAlg_iff` (:488).

So for `S` adelic:
`logVol(LGP·hull(vcI)) = −sFactor(nC)·absLogQ + logVol(hull(vcI))`.
The L5 paper shape `V = ((l+5)/4)·D_exact` requires identifying
`logVol(hull(vcI))` and `D_exact`; this file records the arithmetic identities
(sFactor formula, LGP shift) and the provenance.  Full lana build: the
`IdentifiedCopies` dependency closure has 205 missing oleans (Wall/Concrete/
Cor312/Implication/Anabelian), not built in this session; L5 is NOT closed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1L5IdentificationActual

open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open scoped BigOperators

/-- Green sum-of-squares identity re-exported from A763 (proved there). -/
theorem sum_sq_range_green (n : ℕ) :
    (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sFactor_eq_avg_sq' (n : ℕ) (hn : 0 < n) :
    sFactor n = ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  unfold sFactor
  rw [sum_sq_range_green]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

theorem sFactor_eq_l (n : ℕ) (hn : 0 < n) (l : ℝ) (hl : l = 2 * (n : ℝ) + 1) :
    sFactor n = l * (l + 1) / 12 := by
  rw [sFactor_eq_avg_sq' n hn, hl]
  ring

/-- The LGP shift in lana form: `logVol(LGP·O) = −sFactor·absLogQ`. -/
def lgpIntegralLogVol (sF absLogQ : ℝ) : ℝ := -(sF * absLogQ)

theorem lgpIntegralLogVol_eq (sF absLogQ : ℝ) :
    lgpIntegralLogVol sF absLogQ = -(sF * absLogQ) := rfl

/-- LGP law shape (conditional): `logVol(LGP·S) = logVol(LGP·O)+logVol(S)`. -/
theorem lgpLaw_apply (logLgpS logLgpO logS : ℝ)
    (h : logLgpS = logLgpO + logS) : logLgpS = logLgpO + logS := h

/-- Paper L5 shape. -/
def L5Shape (l D V : ℝ) : Prop := V = ((l + 5) / 4) * D

theorem L5Shape_iff (l D V : ℝ) : L5Shape l D V ↔ V = ((l + 5) / 4) * D := Iff.rfl

/-- Conditional L5 from the LGP law and the paper identification of
`logVol(LGP·O)+logVol(hull)` with `((l+5)/4)D`. -/
theorem L5_of_lgpLaw (V l D : ℝ)
    (h : V = ((l + 5) / 4) * D) : L5Shape l D V := h

def l5Rows : List (String × String × String) :=
  [ ("lana LGP law", "logVol_lgp (IdentifiedCopies.lean:281)", "SOURCE READ; olean absent"),
    ("lana LGP integral", "logVol_lgp_integral (:444): -sFactor(nC)*absLogQ", "SOURCE READ"),
    ("lana component scale", "componentVol_scaleElt (:295): -j² ord_p(q) log p", "SOURCE READ"),
    ("lana idAlg", "idAlg_lgpLaw (:479), wall_idAlg_iff (:488)", "SOURCE READ"),
    ("sFactor formula", "sFactor n = l(l+1)/12 at l=2n+1", "PROVED (sFactor_eq_l)"),
    ("LGP shift arithmetic", "logVol(LGP·O) = -sF*absLogQ", "DEF/PROVED"),
    ("L5 shape", "V = ((l+5)/4)D (conditional)", "DEF/conditional PROVED (L5_of_lgpLaw)"),
    ("build status", "IdentifiedCopies closure: 205 missing oleans (Wall/Concrete/Cor312/Implication/Anabelian)", "NOT BUILT"),
    ("L5 closed?", "NO: needs actual V/hull/D_exact identification from LGP laws", "GAP") ]

theorem l5Rows_length : l5Rows.length = 9 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1L5IdentificationActual.sFactor_eq_l
#print axioms LeanFormal.IUT.XiFPaper.Mzk1L5IdentificationActual.lgpIntegralLogVol_eq

end LeanFormal.IUT.XiFPaper.Mzk1L5IdentificationActual

end