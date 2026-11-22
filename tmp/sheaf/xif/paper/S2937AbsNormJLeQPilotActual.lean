import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2749SupportEqualityActual
import tmp.sheaf.xif.paper.S2743SupportIdealAbsNormLowerActual
import tmp.sheaf.xif.paper.S2739FinsetSupportActual
import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import tmp.sheaf.xif.paper.S2933PerTripleThetaCertificateActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open scoped nonZeroDivisors BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2749SupportEqualityActual
open LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2937AbsNormJLeQPilotActual

variable {l : PrimeGeFive}

/-- Internal absNorm comparison from S2752_hweightvol: the ABC-support ideal
absNorm is at most the q-pilot extended line-bundle absNorm. -/
theorem S2937_absNorm_J_le_qPilot (a b c : Nat) (habc : IsABCTriple a b c) :
    (Ideal.absNorm (S2752J l a b c) : Rat) <=
      FractionalIdeal.absNorm (qPilotLineBundleExtended (l := l) (S2752J l a b c)) := by
  have hfrac : ((Ideal.absNorm (S2752J l a b c) : Nat) : Rat) <=
      FractionalIdeal.absNorm (S2752J l a b c : FractionalIdeal
        (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) := by
    rw [FractionalIdeal.coeIdeal_absNorm]
  have hext : FractionalIdeal.absNorm (S2752J l a b c : FractionalIdeal
      (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) <=
      FractionalIdeal.absNorm (qPilotLineBundleExtended (l := l) (S2752J l a b c)) := by
    rw [show qPilotLineBundleExtended (l := l) (S2752J l a b c) =
        ((qPilotIdeal (l := l) * S2752J l a b c : Ideal (SourceOK (S2735Arithmetic l))) :
          FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic l)))
            (S2735Arithmetic l).K) from rfl]
    rw [S2751_extended_absNorm]
    have hc1 : (1 : Rat) <= FractionalIdeal.absNorm (qPilotIdeal (l := l) :
        FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic l)))
          (S2735Arithmetic l).K) := by
      rw [show (qPilotIdeal (l := l) : FractionalIdeal
          (nonZeroDivisors (SourceOK (S2735Arithmetic l))) (S2735Arithmetic l).K) =
          qPilotLineBundle l from rfl]
      rw [qPilotFractional_absNorm]
      norm_num
    nlinarith
  exact le_trans hfrac hext

/-- S2921S is at most S2921Q: both are logs, and the underlying absNorms are
ordered by S2937. -/
theorem S2937_S2921S_le_S2921Q (a b c : Nat) (habc : IsABCTriple a b c) :
    S2921S a b c <= S2921Q a b c := by
  unfold S2921S S2921Q
  rw [S2736QPilotLineBundleLogVolume_eq]
  apply Real.log_le_log
  · have h1 : (Finset.prod (arithmeticPrimeSupport (abcRationalPoint a c))
        (fun p => p)) = natRadical (a * b * c) :=
      S2749_prod_support_eq_radical habc
    have h2 : (Finset.prod (arithmeticPrimeSupport (abcRationalPoint a c))
        (fun p => p)) =
        (Finset.univ.prod (fun i : SupportIndex (abcRationalPoint a c) => i.1)) := by
      simpa using (Finset.prod_attach
        (s := arithmeticPrimeSupport (abcRationalPoint a c))
        (f := fun p => p)).symm
    have h3 := S2743_prod_support_le_supportIdeal_absNorm
      (K := (S2735Arithmetic S2771FiveLabel).K) (abcRationalPoint a c)
    have hrad : natRadical (a * b * c) <= Ideal.absNorm (S2752J S2771FiveLabel a b c) := by
      rw [← h1]
      simpa [S2752J, h2] using h3
    have hpos : 0 < natRadical (a * b * c) := natRadical_pos (a * b * c)
    have : 0 < Ideal.absNorm (S2752J S2771FiveLabel a b c) := lt_of_lt_of_le hpos hrad
    exact_mod_cast this
  · exact_mod_cast S2937_absNorm_J_le_qPilot (l := S2771FiveLabel) a b c habc

#check S2937_absNorm_J_le_qPilot
#check S2937_S2921S_le_S2921Q
#print axioms S2937_absNorm_J_le_qPilot
#print axioms S2937_S2921S_le_S2921Q

end LeanFormal.IUT.XiFPaper.S2937AbsNormJLeQPilotActual
end