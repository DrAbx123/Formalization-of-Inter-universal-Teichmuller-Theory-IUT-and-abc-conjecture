import tmp.sheaf.xif.paper.S2743SupportIdealAbsNormLowerActual
import tmp.sheaf.xif.paper.S2749SupportEqualityActual
import tmp.sheaf.xif.paper.S2751ExtendedAbsNormActual
import tmp.sheaf.xif.paper.S2743ConditionalHweightvolActual
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual
open LeanFormal.IUT.XiFPaper.S2749SupportEqualityActual
open LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual
open LeanFormal.IUT.XiFPaper.S2743ConditionalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual

variable {l : PrimeGeFive}

noncomputable def S2752J (l : PrimeGeFive) :
    Nat -> Nat -> Nat -> Ideal (SourceOK (S2735Arithmetic l)) :=
  fun a b c => supportIdeal (K := (S2735Arithmetic l).K) (abcRationalPoint a c)

theorem S2752_hweightvol (l : PrimeGeFive) :
    S2736QPilotLineBundleHweightvol (l := l) (S2752J l) 0 := by
  refine S2743ConditionalHweightvol (l := l) (S2752J l) ?_
  intro a b c habc
  have hrad : natRadical (a * b * c) <= Ideal.absNorm (S2752J l a b c) := by
    have h1 : (Finset.prod (arithmeticPrimeSupport (abcRationalPoint a c)) (fun p => p)) = natRadical (a * b * c) :=
      S2749_prod_support_eq_radical habc
    have h2 : (Finset.prod (arithmeticPrimeSupport (abcRationalPoint a c)) (fun p => p)) =
        (Finset.univ.prod (fun i : SupportIndex (abcRationalPoint a c) => i.1)) := by
      simpa using (Finset.prod_attach
        (s := arithmeticPrimeSupport (abcRationalPoint a c))
        (f := fun p => p)).symm
    have h3 := S2743_prod_support_le_supportIdeal_absNorm (K := (S2735Arithmetic l).K) (abcRationalPoint a c)
    rw [← h1]
    simpa [S2752J, h2] using h3
  have hfrac : (natRadical (a * b * c) : Rat) <= FractionalIdeal.absNorm (S2752J l a b c : FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) := by
    rw [FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast hrad
  have hext : FractionalIdeal.absNorm (S2752J l a b c : FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) <=
      FractionalIdeal.absNorm (qPilotLineBundleExtended (l := l) (S2752J l a b c)) := by
    rw [show qPilotLineBundleExtended (l := l) (S2752J l a b c) =
        ((qPilotIdeal (l := l) * S2752J l a b c : Ideal (SourceOK (S2735Arithmetic l))) : FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) from rfl]
    rw [S2751_extended_absNorm]
    have hc1 : (1 : Rat) <= FractionalIdeal.absNorm (qPilotIdeal (l := l) : FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) := by
      rw [show (qPilotIdeal (l := l) : FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) = qPilotLineBundle l from rfl]
      rw [qPilotFractional_absNorm]
      norm_num
    nlinarith
  exact le_trans hfrac hext

end LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
end
