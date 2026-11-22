import tmp.sheaf.xif.paper.S2851A6D6GeometryActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S2848D6F6CompleteActual
import tmp.sheaf.xif.paper.S2812IsStackActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2854StackAutoFromSchemeActual

open LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual
open LeanFormal.IUT.XiFPaper.S2848D6F6CompleteActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2812IsStackActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _

/-- A scheme endomorphism of the D6 representing scheme induces an endomorphism
of the realized hyperbolic orbicurve's stack. -/
noncomputable def S2854StackAuto (α : S2844X ⟶ S2844X) :
    S2851HyperbolicOrbicurve.Hom S2851HyperbolicOrbicurve :=
  S1742StrongTransOfHom (F := K) α

#check S2854StackAuto
#print axioms S2854StackAuto

end LeanFormal.IUT.XiFPaper.S2854StackAutoFromSchemeActual
end
