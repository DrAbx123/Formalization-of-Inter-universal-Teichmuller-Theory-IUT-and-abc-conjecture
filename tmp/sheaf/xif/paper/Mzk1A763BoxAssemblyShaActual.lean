import tmp.sheaf.xif.paper.Mzk1ShellCoeffComputationActual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import Mathlib.Tactic

/-!
# A812 box assembly + A763 bookkeeping (shehdd)

Box-assembly bookkeeping between the paper coefficient and the P7 capsule coefficient:

* `sum_sq_range`: `Σ_{j<n}(j+1)^2 = n(n+1)(2n+1)/6`;
* **`sFactor_eq_sL`**: `sFactor n = sL (2n+1)`, i.e. the lana capsule coefficient is
  exactly the paper hull coefficient `sL l = l(l+1)/12` at `l = 2nC+1` (P7 calibration);
* **`a763_box_szpiro`**: combining `sFactor_eq_sL` with `Mzk1FinalBoundarySzpiroActual.szpiro6_of_ssIneq`
  turns `SSIneqExplicit (sFactor nC) logq l V` + the `c_V=1/4` hull upper bound
  `V ≤ cVModel·l·logdf + E` into `Szpiro6Shape C logq logdf` with the explicit `C`;
* A763 constants re-exported: `cVModel = 1/4`, `szpiroThreshold cVModel = 6`.

Still PENDING (not asserted): the hull upper bound `V ≤ (1/4)l·logdf + C0` itself, and the
exact lana `2l` normalization to the A763 `c_V` claim (`szpiroThreshold` bookkeeping is
green, the geometric upper bound is the open item).  No RETRACTED use.
No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A763BoxAssemblyShaActual

open LeanFormal.IUT.XiFPaper.Mzk1ShellCoeffComputationActual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open scoped BigOperators

/-- Sum of squares: `Σ_{j<n}(j+1)^2 = n(n+1)(2n+1)/6`. -/
theorem sum_sq_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

/-- **P7/A763 calibration**: `sFactor n = sL (2n+1)` (`sL l = l(l+1)/12`). -/
theorem sFactor_eq_sL (n : ℕ) (hn : 0 < n) :
    sFactor n = sL (2 * (n : ℝ) + 1) := by
  unfold sFactor sL
  rw [sum_sq_range]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp [hnR]
  ring

/-- A763 constant re-export: `c_V = 1/4`. -/
theorem a763_cV_eq_quarter : cVModel = 1 / 4 := cVModel_eq

/-- A763 constant re-export: `σ* = 24 c_V = 6`. -/
theorem a763_threshold_six : szpiroThreshold cVModel = 6 := cVModel_szpiroThreshold

/-- **Box assembly**: the P7 capsule coefficient `sFactor nC = sL (2nC+1)` plus the
`c_V = 1/4` hull upper bound turns SSIneq into the explicit Szpiro-6 shape with
constant `2*C0` (hull's `ssIneqExplicit_to_szpiro6`). -/
theorem a763_box_szpiro {nC : ℕ} {l logq V logdf C0 : ℝ}
    (hnC : 0 < nC) (hcast : l = 2 * (nC : ℝ) + 1)
    (hl : 12 ≤ l) (hC0 : 0 ≤ C0) (hdf : 0 ≤ logdf)
    (hVup : V ≤ (1 / 4) * l * logdf + C0)
    (hss : SSIneqExplicit (sFactor nC) logq l V) :
    Szpiro6Shape logq logdf (2 * C0) := by
  have hsC : sFactor nC = l * (l + 1) / 12 := by
    have h1 : sFactor nC = sL (2 * (nC : ℝ) + 1) := sFactor_eq_sL nC hnC
    rw [← hcast] at h1
    unfold sL at h1
    exact h1
  exact ssIneqExplicit_to_szpiro6 (sC := sFactor nC) (logq := logq)
    (logdf := logdf) (l := l) (V := V) (C0 := C0) hsC hl hC0 hdf hVup hss
structure BoxRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def boxRows : List BoxRow :=
  [ ⟨"sum of squares", "Σ_{j<n}(j+1)^2 = n(n+1)(2n+1)/6", "PROVED"⟩
  , ⟨"sFactor = sL", "sFactor n = sL (2n+1) (P7 calibration)", "PROVED"⟩
  , ⟨"c_V", "cVModel = 1/4", "GREEN re-export"⟩
  , ⟨"Szpiro threshold", "szpiroThreshold cVModel = 6", "GREEN re-export"⟩
  , ⟨"box assembly", "SSIneq(sFactor nC) + V <= (1/4)l logdf + E -> Szpiro6Shape C (explicit C)", "PROVED_CONDITIONAL"⟩
  , ⟨"hull upper bound", "V <= (1/4)l logdf + C0", "PENDING (hull open item)"⟩
  , ⟨"scope", "A763 bookkeeping + conditional box; no fake bound; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem boxRows_length : boxRows.length = 7 := rfl

theorem boxRows_has_pending :
    boxRows.any (fun r => r.status = "PENDING (hull open item)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1A763BoxAssemblyShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1A763BoxAssemblyShaActual.sum_sq_range
#print axioms LeanFormal.IUT.XiFPaper.Mzk1A763BoxAssemblyShaActual.sFactor_eq_sL
#print axioms LeanFormal.IUT.XiFPaper.Mzk1A763BoxAssemblyShaActual.a763_box_szpiro
