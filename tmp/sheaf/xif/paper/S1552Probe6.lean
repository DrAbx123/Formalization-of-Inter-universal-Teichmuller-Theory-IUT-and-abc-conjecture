import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace Probe6
variable (P : NumberField.FinitePlace ℚ)

#check @AlgEquiv.toRingEquiv
#check @AlgEquiv.toAddEquiv
#check @AlgEquiv.toRingHom
#check @AlgEquiv.toEquiv
#check (AlgEquiv.toRingEquiv (rationalCompletionPadicEquiv P))
#check (AlgEquiv.toAddEquiv (rationalCompletionPadicEquiv P))
#check (AlgEquiv.toRingHom (rationalCompletionPadicEquiv P))
#check (AlgEquiv.toEquiv (rationalCompletionPadicEquiv P))
#check (rationalCompletionPadicEquiv P).symm
#check (AlgEquiv.toRingEquiv (rationalCompletionPadicEquiv P).symm)

end Probe6
