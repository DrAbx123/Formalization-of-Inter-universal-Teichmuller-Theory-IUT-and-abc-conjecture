import tmp.sheaf.xif.paper.S2780LineBundleABCBridgeActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2743SupportIdealAbsNormLowerActual
import tmp.sheaf.xif.paper.S2796SupportAbsNormLeRadSqActual
import tmp.sheaf.xif.paper.S2751ExtendedAbsNormActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2796SupportAbsNormLeRadSqActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge

/-- Degree-normalized region volume: half of the line-bundle log volume. -/
noncomputable def S2792RegionVolume (a b c : Nat) : Real :=
  (1 / 2) * S2780RegionVolume (a := a) (b := b) (c := c)

/-- Normalized region-weight gap (no height claim). -/
def S2792RegionWeightGap (eps : Real) : Prop :=
  exists D : Real, forall a b c : Nat, IsABCTriple a b c ->
    (1 + eps) * S2792RegionVolume a b c <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D

/-- Conditional actual assembly: if the normalized region volume is bounded by
the weight, the normalized region-weight gap holds with D = 0. -/
theorem S2792RegionWeightGap_of_bound (eps : Real)
    (heps : 0 <= eps)
    (h : forall a b c : Nat, IsABCTriple a b c ->
      S2792RegionVolume a b c <= arithmeticWeight (abcRationalPoint a c)) :
    S2792RegionWeightGap eps := by
  refine ⟨0, ?_⟩
  intro a b c habc
  have h1 := h a b c habc
  have hnn : 0 <= 1 + eps := by linarith
  have := mul_le_mul_of_nonneg_left h1 hnn
  linarith


/-- The additive constant 1/2 log(5^2 * 2161^2). -/
noncomputable def S2792D : Real :=
  (1 / 2) * Real.log ((5 * 5 * 2161 * 2161 : Nat) : Real)

theorem S2792_regionVolume_le_weight_add_D
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2792RegionVolume a b c
      <= arithmeticWeight (abcRationalPoint a c) + S2792D := by
  let l : PrimeGeFive := fiveLabel
  let J : Ideal (SourceOK (A := S2735Arithmetic l)) := S2752J l a b c
  let Jf : FractionalIdeal (nonZeroDivisors (SourceOK (A := S2735Arithmetic l)))
      (S2735Arithmetic l).K := (J : FractionalIdeal _ _)
  let Af : FractionalIdeal (nonZeroDivisors (SourceOK (A := S2735Arithmetic l)))
      (S2735Arithmetic l).K :=
    (qPilotIdeal (l := l) : FractionalIdeal _ _)
  have hnormQ : FractionalIdeal.absNorm
      (qPilotLineBundleExtended (l := l) J)
      = FractionalIdeal.absNorm Af * FractionalIdeal.absNorm Jf := by
    rw [show qPilotLineBundleExtended (l := l) J
        = ((qPilotIdeal (l := l) * J : Ideal (SourceOK (A := S2735Arithmetic l)))
            : FractionalIdeal _ _) from rfl]
    rw [S2751_extended_absNorm]
  have hA : FractionalIdeal.absNorm Af = (5 * 5 * 2161 * 2161 : Rat) := by
    simpa [Af, qPilotLineBundle] using qPilotFractional_absNorm (l := l)
  have hJle : Ideal.absNorm J <= (natRadical (a * b * c)) ^ 2 := by
    dsimp only [J, S2752J]
    change Ideal.absNorm (supportIdeal (K := GaussianField) (abcRationalPoint a c)) <= (natRadical (a * b * c)) ^ 2
    exact S2796_absNorm_supportIdeal_le_radSq habc
  have hJpos_prod : 0 < ∏ i : SupportIndex (abcRationalPoint a c), i.1 := by
    apply Finset.prod_pos
    intro i _
    exact Nat.Prime.pos (prime_of_mem_arithmeticPrimeSupport i.2)
  have hJpos : 0 < Ideal.absNorm J :=
    lt_of_lt_of_le hJpos_prod
      (S2743_prod_support_le_supportIdeal_absNorm
        (K := (S2735Arithmetic l).K) (abcRationalPoint a c))
  have hJfpos : (0 : Rat) < FractionalIdeal.absNorm Jf := by
    rw [show FractionalIdeal.absNorm Jf = ((Ideal.absNorm J : Nat) : Rat) from
      FractionalIdeal.coeIdeal_absNorm J]
    exact_mod_cast hJpos
  have hApos : (0 : Real) < ((5 * 5 * 2161 * 2161 : Rat) : Real) := by norm_num
  have hBpos : (0 : Real) < (FractionalIdeal.absNorm Jf : Rat) := by
    exact_mod_cast hJfpos
  have hBle : (FractionalIdeal.absNorm Jf : Rat) <=
      (((natRadical (a * b * c)) ^ 2 : Nat) : Rat) := by
    rw [show FractionalIdeal.absNorm Jf = ((Ideal.absNorm J : Nat) : Rat) from
      FractionalIdeal.coeIdeal_absNorm J]
    exact_mod_cast hJle
  have hBleR : (FractionalIdeal.absNorm Jf : Real) <=
      ((natRadical (a * b * c) : Real)) ^ 2 := by
    have hcast : (((natRadical (a * b * c)) ^ 2 : Nat) : Real) =
        ((natRadical (a * b * c) : Real)) ^ 2 := by push_cast; ring
    rw [← hcast]
    exact_mod_cast hBle
  have hvol : S2780RegionVolume a b c
      = Real.log ((((5 * 5 * 2161 * 2161 : Rat) : Real))
          * (FractionalIdeal.absNorm Jf : Real)) := by
    unfold S2780RegionVolume
    rw [show S2736QPilotLineBundleLogVolume (l := l)
        (S2752J l a b c)
        = Real.log ((FractionalIdeal.absNorm
            (qPilotLineBundleExtended (l := l) J) : Rat) : Real) from rfl]
    rw [hnormQ, hA]
    congr 1
    push_cast
    ring
  have hprod_le : ((((5 * 5 * 2161 * 2161 : Rat) : Real))
        * (FractionalIdeal.absNorm Jf : Real))
      <= (((5 * 5 * 2161 * 2161 : Rat) : Real))
        * ((natRadical (a * b * c) : Real)) ^ 2 :=
    mul_le_mul_of_nonneg_left hBleR (le_of_lt hApos)
  have hlog_le : Real.log ((((5 * 5 * 2161 * 2161 : Rat) : Real))
        * (FractionalIdeal.absNorm Jf : Real))
      <= Real.log ((((5 * 5 * 2161 * 2161 : Rat) : Real))
        * ((natRadical (a * b * c) : Real)) ^ 2) := by
    apply Real.log_le_log
    · exact mul_pos hApos hBpos
    · exact hprod_le
  have hlogA : Real.log (((5 * 5 * 2161 * 2161 : Rat) : Real))
      = Real.log ((5 * 5 * 2161 * 2161 : Nat) : Real) := by norm_num
  have hlog_rad : Real.log ((((5 * 5 * 2161 * 2161 : Rat) : Real))
        * ((natRadical (a * b * c) : Real)) ^ 2)
      = Real.log ((5 * 5 * 2161 * 2161 : Rat) : Real)
        + 2 * Real.log ((natRadical (a * b * c) : Real)) := by
    rw [Real.log_mul (ne_of_gt hApos) (by positivity)]
    rw [Real.log_pow]
    norm_num
  have hweight : arithmeticWeight (abcRationalPoint a c)
      = Real.log ((natRadical (a * b * c) : Real)) :=
    arithmeticWeight_abcRationalPoint habc
  rw [S2792RegionVolume, hvol, S2792D, hweight]
  have hmul := mul_le_mul_of_nonneg_left hlog_le (show (0 : Real) <= 1 / 2 by norm_num)
  norm_num at hmul hlog_rad ⊢
  linarith [hmul, hlog_rad]

/-- Unconditional normalized region-weight gap, with D = (1+eps) * S2792D. -/
theorem S2792RegionWeightGap_actual (eps : Real) (heps : 0 <= eps) :
    S2792RegionWeightGap eps := by
  refine ⟨(1 + eps) * S2792D, ?_⟩
  intro a b c habc
  have h := S2792_regionVolume_le_weight_add_D a b c habc
  have hnn : 0 <= 1 + eps := by linarith
  have hmul := mul_le_mul_of_nonneg_left h hnn
  nlinarith [hmul]


end LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
end
