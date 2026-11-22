import tmp.sheaf.xif.paper.S2253LinearDisjointActual
import Mathlib.FieldTheory.LinearDisjoint
noncomputable section
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2260IntersectionBotActual
open LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open IntermediateField Module
/-- **Executable route**: a degree-product equality for the two images implies
the intersection is Q.  No Galois hypothesis is needed for this direction. -/
theorem s2260IntersectionIsBot_of_finrank_sup
    [FiniteDimensional ℚ ↥s2253FImage]
    [FiniteDimensional ℚ ↥s2253LImage]
    (h : Module.finrank ℚ ↥(s2253FImage ⊔ s2253LImage) =
      Module.finrank ℚ ↥s2253FImage * Module.finrank ℚ ↥s2253LImage) :
    s2253IntersectionIsBot := by
  change s2253FImage ⊓ s2253LImage = ⊥
  exact (IntermediateField.LinearDisjoint.of_finrank_sup h).inf_eq_bot
/-- The exact missing degree product equality. -/
def s2260DegreeProduct : Prop :=
  Module.finrank ℚ ↥(s2253FImage ⊔ s2253LImage) =
    Module.finrank ℚ ↥s2253FImage * Module.finrank ℚ ↥s2253LImage
/-- Finiteness of the F' image is still a separate degree input. -/
def s2260FImageFinite : Prop :=
  FiniteDimensional ℚ ↥s2253FImage
/-- Finiteness of the Q(E[5]) image. -/
def s2260LImageFinite : Prop :=
  FiniteDimensional ℚ ↥s2253LImage
/-- Exact missing intersection equality. -/
def s2260IntersectionIsBot : Prop :=
  s2253IntersectionIsBot
#print axioms s2260IntersectionIsBot_of_finrank_sup
end LeanFormal.IUT.XiFPaper.S2260IntersectionBotActual
end
