import tmp.sheaf.xif.paper.S2593TensorNormActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalHeight

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2593TensorNormActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2723GlobalProductFormulaActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The finite support index of the actual ABC point `a/c`. -/
abbrev S2723SupportIndex (a c : Nat) : Type :=
  {q : Nat // q ∈ arithmeticPrimeSupport (abcRationalPoint a c)}

/-- A global product-formula datum over the **whole** arithmetic prime support.
It is not a single-place norm: it supplies one actual local tensor point for
each `q` in the support, a product formula for the global point, and the
local logarithmic identity (one summand of the weighted valuation sum). -/
structure S2723GlobalProductFormula (a n c : Nat) where
  /-- Actual local tensor point at each support prime. -/
  localPoint : S2723SupportIndex a c → qVFamTensorBlock T b
  /-- Each local norm is nonzero (needed for the product log). -/
  local_norm_pos : ∀ q, 0 < ‖localPoint q‖
  /-- The global S2588 point norm is the product of the local norms. -/
  norm_eq_product :
    ‖S2588PointMap T b a n c‖ = ∏ q : S2723SupportIndex a c, ‖localPoint q‖
  /-- The local negative log is the `max 0 (-v_q)` summand of the weighted
valuation sum at the support prime `q`. -/
  local_log_eq : ∀ q : S2723SupportIndex a c,
    -Real.log ‖localPoint q‖ =
      max 0 (-(padicValRat q.1 (abcRationalPoint a c) : Real)) *
        Real.log (q.1 : Real)

/-- The global negative log of the S2588 point equals the full sum over the
arithmetic prime support of the weighted `max 0 (-v_q)` terms.  This is the
global sum-over-support object that the single S2593 point norm cannot supply. -/
theorem S2723_neg_log_eq_sum_over_support
    (a n c : Nat) (F : S2723GlobalProductFormula T b a n c) :
    -Real.log ‖S2588PointMap T b a n c‖ =
      ∑ q : S2723SupportIndex a c,
        max 0 (-(padicValRat q.1 (abcRationalPoint a c) : Real)) *
          Real.log (q.1 : Real) := by
  rw [F.norm_eq_product]
  rw [Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    exact F.local_log_eq q
  · intro q _
    exact ne_of_gt (F.local_norm_pos q)

#check S2723GlobalProductFormula
#check S2723_neg_log_eq_sum_over_support
#print axioms S2723_neg_log_eq_sum_over_support

end LeanFormal.IUT.XiFPaper.S2723GlobalProductFormulaActual
end
