/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TraceDualVolumeActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualLattice

/-!
# General trace-dual volume: exact conditional bridge (task-104)

Status: CONDITIONAL INTERFACE + scalar block re-export.  The general
`B4/B5` route needs the SNF/determinant-Haar bridge
`mu(B • O) = |det B|_p * mu(O)` and its dual `(B O)# = B^{-T} O#`.
The file records the exact scalar conditions under which the product
identity and its log form follow; it does NOT claim the general SNF bridge.
-/

noncomputable section
open MeasureTheory ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1GeneralDualVolumeActual

universe u

variable {M : Type u} [AddCommGroup M] [MeasurableSpace M]

/-- Exact relative Haar scaling condition for a pair of lattices `L,O`.
This is the **remaining GAP** of the general B4 route: it must be proved
from SNF/`measure_prime_smul` and the actual trace dual; here it is an
explicit hypothesis, not a green theorem. -/
def RelativeHaarScaling
    (μ : MeasureTheory.Measure M) (L O : AddSubgroup M) (c : ℝ≥0∞) : Prop :=
  μ (L : Set M) = c * μ (O : Set M)

/-- Product identity from the two exact relative scalings.  This is the
arithmetic core of (B4); the missing mathematical content is the actual
det-Haar/SNF proof of the hypotheses, not this cancellation. -/
theorem relativeHaarVolume_product_of_scaling
    (μ : MeasureTheory.Measure M) (L O Ldual Odual : AddSubgroup M)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hL : μ (L : Set M) = c * μ (O : Set M))
    (hD : μ (Ldual : Set M) = c⁻¹ * μ (Odual : Set M)) :
    μ (L : Set M) * μ (Ldual : Set M) =
      μ (O : Set M) * μ (Odual : Set M) := by
  rw [hL, hD]
  calc
    c * μ (O : Set M) * (c⁻¹ * μ (Odual : Set M))
        = (c * c⁻¹) * (μ (O : Set M) * μ (Odual : Set M)) := by ring
    _ = μ (O : Set M) * μ (Odual : Set M) := by
      rw [ENNReal.mul_inv_cancel hc0 hctop, one_mul]

/-- Log form: if the four measures are positive/finite and the product
identity holds, then `lambda_O(L) = - lambda_{O#}(L#)`. -/
theorem relativeLogVolume_neg_of_product
    (μ : MeasureTheory.Measure M) (L O Ldual Odual : AddSubgroup M)
    (hprod : μ (L : Set M) * μ (Ldual : Set M) =
      μ (O : Set M) * μ (Odual : Set M))
    (hLpos : 0 < μ (L : Set M)) (hLfin : μ (L : Set M) < ⊤)
    (hOpos : 0 < μ (O : Set M)) (hOfin : μ (O : Set M) < ⊤)
    (hDpos : 0 < μ (Ldual : Set M)) (hDfin : μ (Ldual : Set M) < ⊤)
    (hOdualPos : 0 < μ (Odual : Set M)) (hOdualFin : μ (Odual : Set M) < ⊤) :
    Real.log (μ (L : Set M)).toReal - Real.log (μ (O : Set M)).toReal =
      - (Real.log (μ (Ldual : Set M)).toReal -
          Real.log (μ (Odual : Set M)).toReal) := by
  have h := congrArg (fun z : ℝ≥0∞ => Real.log z.toReal) hprod
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  have hx0 : (μ (L : Set M)).toReal ≠ 0 := (ENNReal.toReal_pos hLpos.ne' hLfin.ne).ne'
  have hy0 : (μ (Ldual : Set M)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hDpos.ne' hDfin.ne).ne'
  have ho0 : (μ (O : Set M)).toReal ≠ 0 := (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hd0 : (μ (Odual : Set M)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hOdualPos.ne' hOdualFin.ne).ne'
  rw [Real.log_mul hx0 hy0, Real.log_mul ho0 hd0] at h
  linarith

def statusRows : List (String × String) :=
  [ ("scalar p^k B4/B5", "proved in Mzk1TraceDualVolumeActual"),
    ("general SNF/det-Haar scaling", "GAP-DET-HAAR"),
    ("dual lattice B^{-T}O#", "GAP-DUAL-TRANSPOSE"),
    ("qVFamTensorBlock specialization", "GAP") ]

theorem statusRows_length : statusRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GeneralDualVolumeActual
