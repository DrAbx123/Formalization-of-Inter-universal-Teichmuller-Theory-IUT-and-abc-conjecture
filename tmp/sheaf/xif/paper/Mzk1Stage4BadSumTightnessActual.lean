import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual

/-! # Mzk1Stage4BadSumTightnessActual (stage4 lane; BadSumWeightBound tightness)

A688 module: TIGHTNESS of the remaining named input.  With full bad support and local
degrees `d_b = 1`, the arithmetic bad sum `Σ_b e_b·(d_b·log p_b)` is EXACTLY `log N`
(`N = a+b+c+1`), so `BadSumWeightBound` is the sharp radical-type arithmetic condition
for `arithmeticWeight = log rad(abc)` (mainline `Mzk1Gap2ArithmeticReductionActual` holds
the geometric<=>arithmetic equivalence).  This makes the tightness explicit; it does not
prove the input (ABC gate NOT passed).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4BadSumTightnessActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Tightness identity: with `d_b = 1` and full bad support, the bad sum is `log N`. -/
theorem badSum_eq_logN
    (e : Bad (nativePlaceSelection T) → Nat) (N : Nat) (hN : 0 < N)
    (hd : ∀ b : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real) = 1)
    (hfull : N = ∏ b : Bad (nativePlaceSelection T), (qVFamTensorP T b) ^ (e b)) :
    (∑ b : Bad (nativePlaceSelection T),
        (e b : Real) *
          ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
            Real.log ((qVFamTensorP T b : Real)))) =
      Real.log (N : Real) := by
  have hprodpos : (0 : Real) < ((∏ b : Bad (nativePlaceSelection T),
      (qVFamTensorP T b) ^ (e b) : Nat) : Real) := by
    have hposNat : 0 < ∏ b : Bad (nativePlaceSelection T), (qVFamTensorP T b) ^ (e b) := by
      apply Finset.prod_pos
      intro b _
      exact pow_pos (Fact.out : Nat.Prime (qVFamTensorP T b)).pos _
    exact_mod_cast hposNat
  have hlogprod : Real.log (((∏ b : Bad (nativePlaceSelection T),
      (qVFamTensorP T b) ^ (e b) : Nat) : Real)) =
      ∑ b : Bad (nativePlaceSelection T),
        (e b : Real) * Real.log ((qVFamTensorP T b : Real)) := by
    rw [Nat.cast_prod]
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro b _
      rw [Nat.cast_pow, Real.log_pow]
    · intro b _
      have hp : ((qVFamTensorP T b : Nat) : Real) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_zero
      have hp' : (((qVFamTensorP T b : Nat) : Real)) ^ (e b) ≠ 0 := pow_ne_zero _ hp
      simpa [Nat.cast_pow] using hp'
  rw [← hfull] at hlogprod
  have hsub : (∑ b : Bad (nativePlaceSelection T),
      (e b : Real) *
        ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
          Real.log ((qVFamTensorP T b : Real)))) =
      ∑ b : Bad (nativePlaceSelection T),
        (e b : Real) * Real.log ((qVFamTensorP T b : Real)) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [hd b, one_mul]
  rw [hsub]
  exact hlogprod.symm

/-- Tightness status: with `d_b = 1` the bad sum equals `log N`; the Geometric<=>arithmetic
equivalence is the mainline theorem `correctedGap2_iff_arith`. -/
def tightnessRows : List (String × String) :=
  [ ("bad sum", "Σ_b e_b·(d_b·log p_b) with d_b = 1 and full support")
  , ("tightness identity", "= log N exactly (PROVED here)")
  , ("geometric<=>arithmetic", "mainline correctedGap2_iff_arith (DONE)")
  , ("named input", "BadSumWeightBound <= (1+ε)·arithmeticWeight + D' (NOT proved; ABC gate NOT passed)")
  ]

/-- The tightness record has four rows. -/
theorem tightnessRows_length : tightnessRows.length = 4 := rfl

#print axioms badSum_eq_logN
#check badSum_eq_logN
#check tightnessRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4BadSumTightnessActual
end
