import tmp.sheaf.xif.paper.S2253LinearDisjointActual
import tmp.sheaf.xif.paper.S2260IntersectionBotActual
import tmp.sheaf.xif.paper.S2005FprimeGroupActual
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.SplittingField.Construction
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2270IntersectionDegreeActual
open LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open LeanFormal.IUT.XiFPaper.S2260IntersectionBotActual
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual
open IntermediateField Module
/-- Finiteness of the F' image, transferred from S1720Field. -/
instance s2270FImageFinite : FiniteDimensional ℚ ↥s2253FImage :=
  LinearEquiv.finiteDimensional
    (IntermediateField.equivMap (⊤ : IntermediateField ℚ S1720Field) s2253EmbedF).toLinearEquiv
/-- Finiteness of the Q(E[5]) image, transferred from its splitting field. -/
instance s2270LImageFinite : FiniteDimensional ℚ ↥s2253LImage :=
  LinearEquiv.finiteDimensional
    (IntermediateField.equivMap (⊤ : IntermediateField ℚ s2216AbsoluteFiveDivisionField) s2253EmbedL).toLinearEquiv
/-- The F' image degree equals the degree of S1720Field. -/
theorem s2270FImage_finrank_eq :
    Module.finrank ℚ ↥s2253FImage = Module.finrank ℚ S1720Field := by
  rw [← IntermediateField.finrank_top' (F := ℚ) (E := S1720Field)]
  exact (IntermediateField.equivMap (⊤ : IntermediateField ℚ S1720Field) s2253EmbedF).toLinearEquiv.finrank_eq.symm
/-- The F' image has degree 12, from S2005. -/
theorem s2270FImage_finrank :
    Module.finrank ℚ ↥s2253FImage = 12 := by
  rw [s2270FImage_finrank_eq]
  exact S2005_finrank
/-- The L image degree equals the absolute 5-division field degree. -/
theorem s2270LImage_finrank_eq :
    Module.finrank ℚ ↥s2253LImage =
      Module.finrank ℚ s2216AbsoluteFiveDivisionField := by
  rw [← IntermediateField.finrank_top' (F := ℚ) (E := s2216AbsoluteFiveDivisionField)]
  exact (IntermediateField.equivMap (⊤ : IntermediateField ℚ s2216AbsoluteFiveDivisionField) s2253EmbedL).toLinearEquiv.finrank_eq.symm
/-- Degree product implies intersection bot, now with finite images available. -/
theorem s2270IntersectionIsBot_of_degreeProduct
    (h : Module.finrank ℚ ↥(s2253FImage ⊔ s2253LImage) =
      Module.finrank ℚ ↥s2253FImage * Module.finrank ℚ ↥s2253LImage) :
    s2253IntersectionIsBot :=
  s2260IntersectionIsBot_of_finrank_sup h
/-- Exact missing: compositum degree equals the product. -/
def s2270DegreeProduct : Prop :=
  Module.finrank ℚ ↥(s2253FImage ⊔ s2253LImage) =
    Module.finrank ℚ ↥s2253FImage * Module.finrank ℚ ↥s2253LImage
/-- Exact missing intersection equality. -/
def s2270IntersectionIsBot : Prop :=
  s2253IntersectionIsBot
#print axioms s2270FImage_finrank_eq
#print axioms s2270FImage_finrank
#print axioms s2270LImage_finrank_eq
#print axioms s2270IntersectionIsBot_of_degreeProduct
end LeanFormal.IUT.XiFPaper.S2270IntersectionDegreeActual
end
