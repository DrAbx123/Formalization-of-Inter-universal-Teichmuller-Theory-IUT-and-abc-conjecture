import tmp.sheaf.xif.paper.Mzk1SSIneqExplicitFormActual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import Mathlib.Tactic

/-!
# A801 Step (xi) minimal statement (shehdd, lana-free)

Compile-able alternative to `Mzk1StepXIMinimalStatementActual` (which needs
`Iut/Wall/MultiContainer.olean`): the minimal Step-(xi) arithmetical shape is stated
with OUR green explicit form, not by importing lana's `SSIneq`:

  `StepXIMinimalStatement sC logq l V := SSIneqExplicit sC logq l V`
  `= ((sC - 1) * (logq / (2*l)) <= V)`.

Proved (no open input, pure arithmetic):
* `stepXIMinimal_iff`: unfolding of the definition;
* `stepXIMinimal_iff_lanaShape`: under the dictionary `logq = 2*l*A`, the statement is
  exactly lana's shape `(sC - 1) * A <= V`;
* `stepXIMinimal_iff_sL`: the κ/sL form `(sL l - 1) * (logq/(2l)) <= V`;
* `capsule_sum_identity`: `Σ_{j<n}((j+1)^2-1) = n·(sFactor n - 1)` (green re-export).

The lana `Wall.SSIneq` bridge (G4) remains PENDING: it needs `sFactor nC` ↔ `sC`,
`absLogQ` ↔ `A`, and `logVol(hull)` ↔ `V` on the same objects (plus archimedean).
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIMinimalStatementShaActual

open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open scoped BigOperators

/-- Minimal Step-(xi) statement in our explicit arithmetic form. -/
def StepXIMinimalStatement (sC logq l V : ℝ) : Prop :=
  SSIneqExplicit sC logq l V

theorem stepXIMinimal_iff (sC logq l V : ℝ) :
    StepXIMinimalStatement sC logq l V ↔
      (sC - 1) * (logq / (2 * l)) ≤ V :=
  Iff.rfl

theorem stepXIMinimal_iff_sL (logq l V : ℝ) :
    StepXIMinimalStatement (sL l) logq l V ↔
      (sL l - 1) * (logq / (2 * l)) ≤ V :=
  Iff.rfl

/-- **Lana-shape dictionary**: with `logq = 2*l*A`, our explicit form is exactly
`(sC - 1) * A <= V` (the shape of lana's `SSIneq` with `A = absLogQ`). -/
theorem stepXIMinimal_iff_lanaShape {sC logq A l V : ℝ} (hl : l ≠ 0)
    (hlogq : logq = 2 * l * A) :
    StepXIMinimalStatement sC logq l V ↔ (sC - 1) * A ≤ V := by
  unfold StepXIMinimalStatement SSIneqExplicit
  rw [hlogq]
  have hdiv : (2 * l * A) / (2 * l) = A := by
    field_simp [hl]
  rw [hdiv]

/-- Per-capsule sum identity (green): `Σ_{j<n}((j+1)^2-1) = n·(sFactor n - 1)`. -/
theorem capsule_sum_identity (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 - 1)) =
      (n : ℝ) * (sFactor n - 1) :=
  shell_sum_identity n hn

/-- Capsule-level form: the j=1 capsule contribution `(1^2-1)` vanishes. -/
theorem capsule_one_zero : (((1 : ℝ) ^ 2) - 1) = 0 := by norm_num

structure MinimalRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def minimalRows : List MinimalRow :=
  [ ⟨"minimal statement", "StepXIMinimalStatement sC logq l V = ((sC-1)*(logq/(2l)) <= V)", "DEF"⟩
  , ⟨"unfolding", "stepXIMinimal_iff", "PROVED"⟩
  , ⟨"lana shape", "logq=2lA -> (sC-1)A <= V (equals lana SSIneq shape)", "PROVED_CONDITIONAL"⟩
  , ⟨"sL form", "stepXIMinimal_iff_sL", "PROVED"⟩
  , ⟨"capsule sum", "Σ_{j<n}((j+1)^2-1) = n(sFactor n - 1)", "PROVED (green re-export)"⟩
  , ⟨"j=1 capsule", "(1^2-1)=0 automatic", "PROVED"⟩
  , ⟨"lana SSIneq bridge (G4)", "sFactor nC<->sC, absLogQ<->A, logVol(hull)<->V (+archimedean)", "PENDING"⟩
  , ⟨"scope", "lana-free; compiles without Iut oleans; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem minimalRows_length : minimalRows.length = 8 := rfl

theorem minimalRows_has_pending :
    minimalRows.any (fun r => r.status = "PENDING") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1StepXIMinimalStatementShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIMinimalStatementShaActual.stepXIMinimal_iff_lanaShape
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIMinimalStatementShaActual.capsule_sum_identity
