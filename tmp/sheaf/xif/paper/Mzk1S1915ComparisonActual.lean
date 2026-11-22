import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.Mzk1QSideExplicitActual
import tmp.sheaf.xif.paper.Mzk1Paper312StatementActual
import tmp.sheaf.xif.paper.Mzk1N3SharedContainerBridgeShaActual
import Mathlib.Tactic

/-!
# A771 S1915 closed form vs q-pilot reading (short path, conditional)

Green ingredients:
* S1915: `s1915ClosedForm T = 1 + Σ_b [K_b:Q_p]·log(rootImageRadius T b)`;
* A762 radius formula: `log(rootImageRadius T b) = -(c_norm_b·log p_b)/(2ℓ)`;
* S2637/QSide: `qPilotLogVolumeReading P = -order·log(residueNormBase place)`
  (and `= Real.log ‖q‖`, strictly negative).

Proved here:
1. `s1915ClosedForm_eq_one_sub_sum`:
   `s1915ClosedForm T = 1 - (1/(2ℓ))·Σ_b d_b·c_norm_b·log p_b`
   with `d_b = [K_b:Q_p]`, `c_norm_b = qVFamNormalizedCoefficient`;
2. explicit q-side closed forms re-exported;
3. the **short-path dictionary** `HullQDictionary T C3 P` with exactly two fields:
   * `theta_eq : thetaPilotHullLogVolumeReal C3 = s1915ClosedForm T`
     (θ carrier alignment: C3 tensor θ-hull vs S1902 product-ball hull);
   * `q_eq_sum : qPilotLogVolumeReading P = -(1/(2ℓ))·Σ_b d_b·c_norm_b·log p_b`
     (single-place q reading vs the sum over bad places);
4. under the dictionary: `s1915ClosedForm = 1 + qReading`, hence
   **`qThetaPilotLogVolumeComparison C3 P` with margin 1**, and `paperGap` on any
   real shared container.

Thus the short path CLOSES the comparison **provided** the two-field dictionary;
the dictionary itself is the remaining gap (no sum-over-places identity is proved).
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerRealActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **S1915 closed form in q-coordinates**:
`1 + Σ_b d_b log(rootImageRadius_b) = 1 - (1/(2ℓ)) Σ_b d_b c_norm_b log p_b`. -/
theorem s1915ClosedForm_eq_one_sub_sum :
    s1915ClosedForm T =
      1 - (1 / (2 * (l.value : Real))) *
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) * (qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real) := by
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) =
        -((1 / (2 * (l.value : Real))) *
          ((s1915LocalDegree T b : Real) * (qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real))) := by
    intro b
    rw [log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL]
    ring
  unfold s1915ClosedForm
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  rw [Finset.sum_neg_distrib, Finset.mul_sum]
  ring

variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The q-pilot reading is the log norm of the actual completion `q`. -/
theorem qReading_eq_log_norm : qPilotLogVolumeReading P = Real.log ‖P.line.C3.q.q‖ :=
  qPilotLogVolumeReading_eq_log_norm P

/-- Strict negativity of the q-pilot reading. -/
theorem qReading_neg : qPilotLogVolumeReading P < 0 :=
  qPilotLogVolumeReading_neg' P

/-- **The short-path dictionary** (exactly two log-volume alignments):
the theta-hull reading equals S1915's closed form, and the single-place q reading
equals the `-(1/(2ℓ))·Σ_b d_b·c_norm_b·log p_b` sum over all bad places. -/
structure HullQDictionary : Prop where
  theta_eq : thetaPilotHullLogVolumeReal C3 = s1915ClosedForm T
  q_eq_sum :
    qPilotLogVolumeReading P =
      -(1 / (2 * (l.value : Real))) *
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) * (qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real)

/-- Under the dictionary, `s1915ClosedForm = 1 + qReading` (margin 1). -/
theorem s1915ClosedForm_eq_one_add_qReading (D : HullQDictionary T C3 P) :
    s1915ClosedForm T = 1 + qPilotLogVolumeReading P := by
  rw [s1915ClosedForm_eq_one_sub_sum, D.q_eq_sum]
  ring

/-- **Short-path comparison**: under the dictionary the paper comparison holds
(with margin 1). -/
theorem qThetaPilotLogVolumeComparison_of_s1915 (D : HullQDictionary T C3 P) :
    qThetaPilotLogVolumeComparison C3 P := by
  unfold qThetaPilotLogVolumeComparison
  rw [D.theta_eq, s1915ClosedForm_eq_one_add_qReading T C3 P D]
  linarith

/-- Consequently the boundary `paperGap` holds on any real shared container. -/
theorem paperGap_of_s1915 (D : HullQDictionary T C3 P)
    (Dc : SharedContainerReal (l := l) (I := I) C3 P) : paperGap Dc := by
  rw [paperGap_iff_qThetaComparison C3 P Dc]
  exact qThetaPilotLogVolumeComparison_of_s1915 T C3 P D

structure S1915Row where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def s1915Rows : List S1915Row :=
  [ ⟨"closed form", "s1915ClosedForm = 1 + Σ_b d_b log rootImageRadius_b", "GREEN (S1915)"⟩
  , ⟨"q-coordinates", "= 1 - (1/(2l)) Σ_b d_b c_norm_b log p_b", "PROVED"⟩
  , ⟨"q reading", "qPilotLogVolumeReading P = -order·log(residueNormBase) = log ‖q‖ < 0", "GREEN (QSide)"⟩
  , ⟨"dictionary theta_eq", "thetaPilotHullLogVolumeReal C3 = s1915ClosedForm T (carrier alignment)", "DICTIONARY_GAP"⟩
  , ⟨"dictionary q_eq_sum", "single-place q reading = sum over bad places", "DICTIONARY_GAP"⟩
  , ⟨"comparison", "dictionary -> qThetaPilotLogVolumeComparison with margin 1", "PROVED_CONDITIONAL"⟩
  , ⟨"paperGap", "dictionary -> paperGap (via bridge)", "PROVED_CONDITIONAL"⟩
  , ⟨"scope", "no toy carrier; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem s1915Rows_length : s1915Rows.length = 8 := rfl

theorem s1915Rows_has_dictionary_gap :
    s1915Rows.any (fun r => r.status = "DICTIONARY_GAP") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual.s1915ClosedForm_eq_one_sub_sum
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual.s1915ClosedForm_eq_one_add_qReading
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual.qThetaPilotLogVolumeComparison_of_s1915
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual.paperGap_of_s1915
