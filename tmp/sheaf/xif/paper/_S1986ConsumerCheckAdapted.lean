import tmp.sheaf.xif.paper.S1986TensorTransportActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S1986ConsumerCheck

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1941ActualQEquationActual
open LeanFormal.IUT.XiFPaper.S1986TensorTransportActual

#check @s1986TensorIntegrality
#check @s1986FirstMissing
#check @s1986HullVolume_eq_zero

-- the actual C3 q equation, derived from the closed first missing
theorem consumer_actualQEquation (l : PrimeGeFive) : S1941ActualQEquation l :=
  (s1941ActualQEquation_iff_firstMissing l).mpr (s1986FirstMissing l)

#print axioms consumer_actualQEquation

end LeanFormal.IUT.XiFPaper.S1986ConsumerCheck
end
