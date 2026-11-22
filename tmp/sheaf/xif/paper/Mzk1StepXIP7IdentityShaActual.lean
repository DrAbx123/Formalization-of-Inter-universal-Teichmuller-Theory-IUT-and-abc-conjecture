import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullShaActual
import tmp.sheaf.xif.paper.Mzk1SSIneqExplicitFormActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-!
# A801/A803 P7 identity: sFactor / (2ℓ) coefficient (shehdd)

P7 asks for the averaged `(sFactor−1)` coefficient and the exact `(2ℓ)` normalization.
Proved here as pure identities:
* `p7_coefficient_identity`: `(sFactor n - 1) * (logq/(2l)) = ((sFactor n -1)/(2l)) * logq`;
* `p7_capsule_average`: `(1/n) Σ_{j<n}((j+1)^2-1) = sFactor n - 1` (green re-export; the
  capsule sum gives exactly the averaged coefficient);
* `p7_scaled_procession`: `(Σ_i scaledClosedFormR((i+1)^2))/n = s1915ClosedForm - sFactorFin n * S`
  (green re-export from the scaled θ-hull file);
* `p7_j1_zero`: capsule j=1 contributes `(1²-1)=0`.

The remaining P7 gap is the exact lana calibration `sFactor n ↔ 2ℓ·c_V` (or the leading
coefficient `c_lana = (sFactor-1)/(2ℓ)` with `c_V = 1/4`, Szpiro threshold 6): this relates
`sFactor` to the A763 constant `c_V` and to lana's `nC`; it is PENDING (not asserted here).
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIP7IdentityShaActual

open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped BigOperators

/-- P7 coefficient identity: `(sFactor-1) * (logq/(2l))` is the `c_lana` form. -/
theorem p7_coefficient_identity (n : ℕ) (logq l : ℝ) (hl : l ≠ 0) :
    (sFactor n - 1) * (logq / (2 * l)) =
      ((sFactor n - 1) / (2 * l)) * logq := by
  field_simp [hl]

/-- P7 averaged capsule coefficient (green): `(1/n)Σ_{j<n}((j+1)^2-1) = sFactor n - 1`. -/
theorem p7_capsule_average (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 - 1)) =
      sFactor n - 1 :=
  shell_average_identity n hn

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- P7 scaled procession average (green re-export): the average of the scaled closed
forms is `s1915ClosedForm - sFactorFin n * S`. -/
theorem p7_scaled_procession (n : ℕ) (hn : 0 < n) :
    (∑ i : Fin n, scaledClosedFormR T (((i : ℝ) + 1) ^ 2)) / (n : ℝ) =
      s1915ClosedForm T - sFactorFin n * qLogSum T :=
  processionAverage_scaledClosedForm T n hn

/-- P7: capsule j=1 contributes `(1²-1)=0` (automatic capsule). -/
theorem p7_j1_zero : (((1 : ℝ) ^ 2) - 1) = 0 := by norm_num

/-- P7: the SSIneq explicit coefficient is exactly `(sC-1)/(2l) * logq`; with
`sC = sFactor n` this is the lana averaged coefficient. -/
theorem p7_ssIneq_explicit_coefficient (n : ℕ) (logq l V : ℝ) (hl : l ≠ 0) :
    SSIneqExplicit (sFactor n) logq l V ↔
      ((sFactor n - 1) / (2 * l)) * logq ≤ V := by
  unfold SSIneqExplicit
  rw [p7_coefficient_identity n logq l hl]

structure P7Row where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def p7Rows : List P7Row :=
  [ ⟨"coefficient identity", "(sFactor n -1)*(logq/(2l)) = ((sFactor n -1)/(2l))*logq", "PROVED"⟩
  , ⟨"capsule average", "(1/n)Σ_{j<n}((j+1)^2-1) = sFactor n -1", "PROVED (green)"⟩
  , ⟨"scaled procession", "avg scaledClosedFormR = s1915ClosedForm - sFactorFin n*S", "PROVED (green)"⟩
  , ⟨"j=1 capsule", "(1^2-1)=0 automatic", "PROVED"⟩
  , ⟨"SSIneq coefficient", "SSIneqExplicit (sFactor n) ... <-> ((sFactor n-1)/(2l))*logq <= V", "PROVED"⟩
  , ⟨"exact sFactor <-> 2l*c_V", "lana nC/c_lana <-> A763 c_V=1/4 bookkeeping", "PENDING"⟩
  , ⟨"scope", "pure identities; no lana import; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem p7Rows_length : p7Rows.length = 7 := rfl

theorem p7Rows_has_pending :
    p7Rows.any (fun r => r.status = "PENDING") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1StepXIP7IdentityShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIP7IdentityShaActual.p7_coefficient_identity
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIP7IdentityShaActual.p7_capsule_average
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIP7IdentityShaActual.p7_scaled_procession
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIP7IdentityShaActual.p7_ssIneq_explicit_coefficient
