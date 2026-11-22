import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
namespace LeanFormal.IUT.XiFPaper.S2489FbarActual

universe u
variable {l : PrimeGeFive}
variable (A : InitialThetaArithmeticData l)

def S2489Fbar : SourceFbarExtension A := SourceFbarExtension.canonical A

#check S2489Fbar

end LeanFormal.IUT.XiFPaper.S2489FbarActual
end