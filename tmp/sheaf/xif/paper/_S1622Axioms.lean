import tmp.sheaf.xif.paper.S1622ZSMulInductionStepActual

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
open LeanFormal.IUT.XiFPaper.S1620ZSMulPointInductionActual

#check LeanFormal.IUT.XiFPaper.S1622ZSMulInductionStepActual.s1622ZSMulPointFormula
#print axioms LeanFormal.IUT.XiFPaper.S1622ZSMulInductionStepActual.s1622ZSMulPointFormula
example : S1620ZSMulPointFormula :=
  LeanFormal.IUT.XiFPaper.S1622ZSMulInductionStepActual.s1622ZSMulPointFormula
end
