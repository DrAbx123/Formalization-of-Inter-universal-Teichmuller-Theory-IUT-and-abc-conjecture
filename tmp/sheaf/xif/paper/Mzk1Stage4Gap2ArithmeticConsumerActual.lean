import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual

/-! # Mzk1Stage4Gap2ArithmeticConsumerActual (stage4 lane; Gap2 arithmetic consumers)

A681 module: stage4 thin consumers of the mainline Gap-2 ARITHMETICIZATION
(`Mzk1Gap2ArithmeticReductionActual`, READ only): geometry eliminated, the pure
bad-sum weight bound, the `log N ≤ log c + log 3` core, and the reduction to the
radical bound.  No conclusion changed; ABC gate NOT passed.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ArithmeticConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Consumer: geometry eliminated — corrected Gap 2 ⇔ pure bad-sum arithmetic bound. -/
theorem stage4_correctedGap2_iff_arith
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal) :
    CorrectedGap2Shape T point eN ↔ BadSumWeightBound T eN :=
  correctedGap2_iff_arith T point eN hc0 hcT hhull

/-- Consumer: the `log N ≤ log c + log 3` core on ABC triples. -/
theorem stage4_logN_le_log_c_add_log3 {a b c : Nat} (habc : IsABCTriple a b c) :
    Real.log (((a + b + c + 1 : Nat)) : Real) ≤ Real.log (c : Real) + Real.log 3 :=
  logN_le_log_c_add_log3 habc

/-- Consumer: corrected Gap 2 reduces to the ABC radical bound. -/
theorem stage4_correctedGap2_reduces_to_radical
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : Real))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hGap2 : CorrectedGap2Shape T point eN) :
    ∀ ε : Real, 0 < ε → ∃ D : Real,
      ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
        Height.logHeight₁ (abcRationalPoint aN cN) ≤
          (1 + ε) * arithmeticWeight (abcRationalPoint aN cN) + D :=
  correctedGap2_reduces_to_radical T point eN hc0 hcT hd hfull hunit hGap2

/-- Consumer: the five-row arithmetic reduction record. -/
theorem stage4_arithReductionRows_length :
    arithReductionRows.length = 5 :=
  arithReductionRows_length

#print axioms stage4_correctedGap2_iff_arith
#print axioms stage4_correctedGap2_reduces_to_radical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith

#check stage4_correctedGap2_iff_arith
#check stage4_logN_le_log_c_add_log3
#check stage4_correctedGap2_reduces_to_radical
#check stage4_arithReductionRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ArithmeticConsumerActual
end
