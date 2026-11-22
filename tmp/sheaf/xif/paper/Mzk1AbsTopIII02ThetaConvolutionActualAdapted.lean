import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum

/-!
# Mzk1AbsTopIII02ThetaConvolutionActualAdapted (adapted copy, A475 reuse) — Gaussian theta convolution model
(AbsTopIII02 object layer, asset-first)

STEP 0 prior-art (reused, no new mathematics):
* Foundations/Theta/GaussianKernel (gaussExponent; thetaValue; realThetaValue;
  realThetaValue_pos; thetaValue_eq_of_eq_neg);
* Foundations/Theta/GaussianSquareSum (gaussianSquareSum / normalizedGaussianDegree).

WHAT THIS FILE DOES:
* defines the Gaussian theta kernel at a q-parameter and its convolution sum;
* proves the kernel's reflection symmetry, convolution nonnegativity and the q=1/2 concrete
  instantiation;
* packages them in a typed AbsTopIII02 convolution model;
* records rows, keeping the paper-level AbsTopIII02 convolution theorem NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII02ThetaConvolutionActualAdapted

open LeanFormal.IUT
open scoped BigOperators

/-- The Gaussian theta kernel at the q-parameter: j ↦ q^(gaussExponent j). -/
def gaussianThetaKernel (q : ℝ) (j : ℤ) : ℝ :=
  realThetaValue q j

/-- The Gaussian theta kernel is symmetric under j ↦ -j. -/
theorem gaussianThetaKernel_neg (q : ℝ) (j : ℤ) :
    gaussianThetaKernel q (-j) = gaussianThetaKernel q j := by
  unfold gaussianThetaKernel realThetaValue
  rw [gaussExponent_neg]

/-- The Gaussian theta kernel is nonnegative for q > 0. -/
theorem gaussianThetaKernel_nonneg {q : ℝ} (hq : 0 < q) (j : ℤ) :
    0 ≤ gaussianThetaKernel q j :=
  (realThetaValue_pos hq j).le

/-- The Gaussian theta convolution sum
C_n(j) = Σ_{k<n} q^(k^2) * q^((j-k)^2) (finite convolution model). -/
def gaussianThetaConvolution (q : ℝ) (j : ℤ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, gaussianThetaKernel q (k : ℤ) * gaussianThetaKernel q (j - (k : ℤ))

/-- The Gaussian theta convolution sum is nonnegative for q > 0. -/
theorem gaussianThetaConvolution_nonneg {q : ℝ} (hq : 0 < q) (j : ℤ) (n : ℕ) :
    0 ≤ gaussianThetaConvolution q j n := by
  unfold gaussianThetaConvolution
  exact Finset.sum_nonneg (fun k _ =>
    mul_nonneg (gaussianThetaKernel_nonneg hq _) (gaussianThetaKernel_nonneg hq _))

/-- The q = 1/2 concrete convolution model: kernel + convolution with q = 1/2. -/
structure AbsTopIII02ConvolutionModel where
  /-- the Gaussian q-parameter. -/
  q : ℝ
  /-- convergence range: q > 0. -/
  q_pos : 0 < q
  /-- convergence range: q < 1. -/
  q_lt_one : q < 1
  /-- the Gaussian theta kernel. -/
  kernel : ℤ → ℝ
  /-- the model's finite convolution sum. -/
  convolution : ℤ → ℕ → ℝ
  /-- kernel symmetry j ↦ -j. -/
  kernel_neg : ∀ j : ℤ, kernel (-j) = kernel j
  /-- convolution nonnegativity. -/
  convolution_nonneg : ∀ j n, 0 ≤ convolution j n

/-- The concrete convolution model at q = 1/2, from the tree Gaussian assets. -/
def absTopIII02ConvolutionModel : AbsTopIII02ConvolutionModel where
  q := 1 / 2
  q_pos := by norm_num
  q_lt_one := by norm_num
  kernel := gaussianThetaKernel (1 / 2)
  convolution := gaussianThetaConvolution (1 / 2)
  kernel_neg := gaussianThetaKernel_neg (1 / 2)
  convolution_nonneg := gaussianThetaConvolution_nonneg (by norm_num)

/-- The AbsTopIII02 convolution model is inhabited. -/
theorem absTopIII02ConvolutionModel_nonempty : Nonempty AbsTopIII02ConvolutionModel :=
  ⟨absTopIII02ConvolutionModel⟩

/-- The concrete model's kernel is the tree real theta value at q = 1/2. -/
theorem absTopIII02ConvolutionModel_kernel_apply (j : ℤ) :
    absTopIII02ConvolutionModel.kernel j = realThetaValue (1 / 2) j := rfl

/-- AbsTopIII02 rows: (paper object, formal asset, status). -/
def absTopIII02Rows : List (String × String × String) :=
  [ ("Gaussian theta kernel", "gaussianThetaKernel; gaussianThetaKernel_neg/nonneg", "CONSTRUCTED/PROVED"),
    ("finite Gaussian theta convolution", "gaussianThetaConvolution; gaussianThetaConvolution_nonneg", "CONSTRUCTED/PROVED"),
    ("q = 1/2 concrete convolution model", "absTopIII02ConvolutionModel", "CONSTRUCTED/INHABITED"),
    ("kernel = tree realThetaValue", "absTopIII02ConvolutionModel_kernel_apply", "PROVED (rfl)"),
    ("Gaussian square-sum normalization", "GaussianSquareSum.gaussianSquareSum (tree)", "TREE ASSET (imported)"),
    ("paper AbsTopIII02 Gaussian/theta convolution theorem", "not asserted: finite model only", "NAMED (paper input)") ]

/-- The AbsTopIII02 row record has six rows. -/
theorem absTopIII02Rows_length : absTopIII02Rows.length = 6 := rfl

#check gaussianThetaKernel
#check gaussianThetaKernel_neg
#check gaussianThetaConvolution
#check gaussianThetaConvolution_nonneg
#check AbsTopIII02ConvolutionModel
#check absTopIII02ConvolutionModel_nonempty
#check absTopIII02Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII02ThetaConvolutionActualAdapted
end
