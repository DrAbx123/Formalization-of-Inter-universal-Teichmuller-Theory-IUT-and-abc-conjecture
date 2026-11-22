import tmp.sheaf.xif.paper.S1964QuotientCFActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

#check sourceTypeOneOnePlusMinus
#check S1964HonestQuotientSignature
#check SourceOrbicurveSignature.typeOneOne
#check SourceOrbicurveSignature.typeOneLTorsion
#check SourceOrbicurveSignature.typeOneLTorsionPlusMinus
#check SourceSignQuotientData.cF_genus
#check SourceSignQuotientData.xK_signature
#check SourceSignQuotientData.cK_signature
#check S1964HonestSignature_ne_paper
#check Iut.OrbicurveSignature.eulerCharacteristic

example : sourceTypeOneOnePlusMinus.eulerCharacteristic = -1/2 := by
  norm_num [sourceTypeOneOnePlusMinus, Iut.OrbicurveSignature.eulerCharacteristic]

example : S1964HonestQuotientSignature.eulerCharacteristic = -1/2 :=
  S1964HonestQuotientSignature_euler
