import tmp.sheaf.xif.paper.Mzk1SzpiroFromBoxActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import tmp.sheaf.xif.paper.Mzk1A763BoxAssemblyShaActual
import Mathlib.Tactic

/-!
# A812/A822 box-coefficient identification (shehdd)

Connects hull's `Mzk1SzpiroFromBoxActual` box coefficient

  `cForm l = (l+1)/24 - 1/(2l)`

to the P7/A763 bookkeeping coefficient `(sL l - 1)/(2l)` and to lana's capsule
coefficient `(sFactor n - 1)/(2l)` at `l = 2n+1`:

* `box_cForm_eq_sL`: `cForm l = (sL l - 1)/(2l)` (`sL l = l(l+1)/12`);
* `box_cForm_eq_sFactor`: at `l = 2n+1`, `cForm l = (sFactor n - 1)/(2l)`;
* `box_ssIneqCoeff_eq_cForm`: the boundary file's SSIneq coefficient
  `(l+1)/24 - 1/(2l)` is exactly `cForm l`.

These are pure arithmetic identities; the geometric box upper bound
`V <= ((l+5)/4)*logdf + C0` remains the open item (hull's A816 chain),
and the `(1+eps(l))` Szpiro form in `Mzk1SzpiroFromBoxActual` is not upgraded to `6`.
No RETRACTED use.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1BoxCoeffIdentificationShaActual

open LeanFormal.IUT.XiFPaper.Mzk1SzpiroFromBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1A763BoxAssemblyShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual
open scoped BigOperators

/-- **A763 box coefficient**: `cForm l = (sL l - 1)/(2ℓ)`. -/
theorem box_cForm_eq_sL (l : ℝ) (hl : l ≠ 0) :
    cForm l = (sL l - 1) / (2 * l) := by
  unfold cForm sL
  field_simp [hl]
  ring

/-- The boundary coefficient `(l+1)/24 - 1/(2l)` is `cForm l`. -/
theorem box_ssIneqCoeff_eq_cForm (l : ℝ) :
    (l + 1) / 24 - 1 / (2 * l) = cForm l := by
  unfold cForm
  ring

/-- **Capsule coefficient**: at `l = 2n+1`, `cForm l = (sFactor n - 1)/(2ℓ)`. -/
theorem box_cForm_eq_sFactor {n : ℕ} {l : ℝ} (hn : 0 < n) (hcast : l = 2 * (n : ℝ) + 1) :
    cForm l = (sFactor n - 1) / (2 * l) := by
  rw [box_cForm_eq_sL l (by rw [hcast]; positivity)]
  have hs : sFactor n = sL l := by
    have h1 : sFactor n = sL (2 * (n : ℝ) + 1) := sFactor_eq_sL n hn
    rw [← hcast] at h1
    exact h1
  rw [hs]

structure BoxCoeffRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def boxCoeffRows : List BoxCoeffRow :=
  [ ⟨"box coefficient", "cForm l = (l+1)/24 - 1/(2l)", "DEF (Mzk1SzpiroFromBoxActual)"⟩
  , ⟨"cForm = (sL-1)/(2l)", "A763 bookkeeping identity", "PROVED"⟩
  , ⟨"boundary coeff = cForm", "(l+1)/24 - 1/(2l) = cForm l", "PROVED"⟩
  , ⟨"cForm = (sFactor-1)/(2l)", "at l=2n+1 (P7 capsule coefficient)", "PROVED"⟩
  , ⟨"geometric box", "V <= ((l+5)/4)logdf + C0", "OPEN (hull A816)"⟩
  , ⟨"plain Szpiro 6", "only (1+eps(l)) form proved in Mzk1SzpiroFromBoxActual", "NOT_CLAIMED"⟩
  , ⟨"scope", "coefficient bookkeeping only; no fake box/ABC; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem boxCoeffRows_length : boxCoeffRows.length = 7 := rfl

theorem boxCoeffRows_has_open :
    boxCoeffRows.any (fun r => r.status = "OPEN (hull A816)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1BoxCoeffIdentificationShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1BoxCoeffIdentificationShaActual.box_cForm_eq_sL
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BoxCoeffIdentificationShaActual.box_cForm_eq_sFactor
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BoxCoeffIdentificationShaActual.box_ssIneqCoeff_eq_cForm
