import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2735CountOptionalAdapted

variable (l : PrimeGeFive)

theorem qPilotLineBundle_count (v : IsDedekindDomain.HeightOneSpectrum (S2735O l)) :
    FractionalIdeal.count (S2735Arithmetic l).K v (qPilotLineBundle l) =
      (if v = qPilotP5plus l then 1 else 0) +
      (if v = qPilotP5minus l then 1 else 0) +
      (if v = qPilotP2161plus l then 1 else 0) +
      (if v = qPilotP2161minus l then 1 else 0) := by
  rw [qPilotLineBundle]
  have hfac :
      qPilotIdeal l =
        (gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
          gaussianField2161Plus * gaussianField2161Minus :
            Ideal (SourceOK (A := S2735Arithmetic l))) := rfl
  rw [hfac]
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_mul]
  rw [FractionalIdeal.count_mul, FractionalIdeal.count_mul, FractionalIdeal.count_mul]
  · rw [FractionalIdeal.count_maximal, FractionalIdeal.count_maximal,
      FractionalIdeal.count_maximal, FractionalIdeal.count_maximal]
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr
      (gaussianFieldFivePrimePlus_isMaximal.ne_bot)
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr
      (gaussianFieldFivePrimeMinus_isMaximal.ne_bot)
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr
      (gaussianField2161Plus_isMaximal.ne_bot)
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr
      (gaussianField2161Minus_isMaximal.ne_bot)


#check qPilotLineBundle_count
#print axioms qPilotLineBundle_count
end LeanFormal.IUT.XiFPaper.S2735CountOptionalAdapted
end
