import tmp.sheaf.xif.paper.S3136LGPJvQSpanTopActual

/-! # Stage-4 host: the candidate J_v Q-span is the full rational line (retry)

Source anchors: IUT III, Prop. 3.7, (ii), (v) (pp. 108--112); IUT III, Prop.
3.2, (ii) (pp. 97--99).

At the exponent level the paper's Q-span = IQ condition has the actual shadow:
the Q-span of the actual theta-value divisor exponents is the full rational
line.  Proof via the standard submodule tools (eq_top_iff, subset_span,
smul_mem) applied to the actual nonzero q_v exponent.

LABEL: prerequisite component only.  Consumer: lattice stream. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPJvQSpanTopActual2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalFractionalIdealCandidate
open LeanFormal.IUT.XiFPaper.S3136LGPJvQSpanTopActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The candidate J_v Q-span is the full rational line. -/
theorem lgpLocalFractionalIdealQSpan_eq_top'
    (b : Bad (nativePlaceSelection T)) :
    lgpLocalFractionalIdealQSpan T b = ⊤ := by
  set c : ℚ := ((lgpQVDivisorExponent T b : ℕ) : ℚ) with hcdef
  have hpos := lgpQVDivisorExponent_pos' T b
  have hne : c ≠ 0 := by
    rw [hcdef]
    exact_mod_cast ne_of_gt hpos
  have hmem0 : ((lgpQVDivisorExponent T b : ℕ) : ℚ) ∈
      lgpLocalFractionalIdealQSpan T b := by
    unfold lgpLocalFractionalIdealQSpan
    apply Submodule.subset_span
    refine ⟨lgpThetaLabelOne l, ?_⟩
    change ((lgpThetaLabelWeight (lgpThetaLabelOne l) *
      lgpQVDivisorExponent T b : ℕ) : ℚ) =
      ((lgpQVDivisorExponent T b : ℕ) : ℚ)
    simp [lgpThetaLabelWeight_one]
  have hmem : c ∈ lgpLocalFractionalIdealQSpan T b := by
    rw [hcdef]
    exact hmem0
  rw [eq_top_iff]
  intro x _
  have hx : x = (x / c) • c := by
    rw [smul_eq_mul]
    exact (div_mul_cancel₀ x hne).symm
  rw [hx]
  exact Submodule.smul_mem (lgpLocalFractionalIdealQSpan T b) (x / c) hmem

#check lgpLocalFractionalIdealQSpan_eq_top'

end LeanFormal.IUT.XiFPaper.S3136LGPJvQSpanTopActual2
end