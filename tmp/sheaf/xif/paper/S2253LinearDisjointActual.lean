import tmp.sheaf.xif.paper.S2216D5QuadraticTransportActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
noncomputable section
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
/-- A common algebraically closed overfield for F' and the absolute 5-division field. -/
abbrev s2253Omega : Type := AlgebraicClosure ℚ
/-- Canonical embedding of F' into the common algebraic closure. -/
noncomputable def s2253EmbedF : S1720Field →ₐ[ℚ] s2253Omega := IsAlgClosed.lift
/-- Canonical embedding of the absolute 5-division field into the common algebraic closure. -/
noncomputable def s2253EmbedL : s2216AbsoluteFiveDivisionField →ₐ[ℚ] s2253Omega := IsAlgClosed.lift
/-- Image of F' in the common algebraic closure. -/
noncomputable def s2253FImage : IntermediateField ℚ s2253Omega :=
  IntermediateField.map s2253EmbedF ⊤
/-- Image of the absolute 5-division field in the common algebraic closure. -/
noncomputable def s2253LImage : IntermediateField ℚ s2253Omega :=
  IntermediateField.map s2253EmbedL ⊤
/-- The actual intersection F' cap Q(E[5]) inside the common algebraic closure. -/
noncomputable def s2253Intersection : IntermediateField ℚ s2253Omega :=
  s2253FImage ⊓ s2253LImage
/-- Exact missing linear-disjointness equality: the intersection is Q. -/
def s2253IntersectionIsBot : Prop :=
  s2253Intersection = ⊥
/-- The actual S2216 linear-disjointness proposition for the constructed embeddings. -/
theorem s2253LinearDisjointness_iff :
    s2216LinearDisjointness s2253Omega s2253EmbedF s2253EmbedL ↔
      s2253IntersectionIsBot :=
  Iff.rfl
/-- The constructed embeddings satisfy the S2216 existential target once the
intersection equality is supplied. -/
theorem s2253LinearDisjointnessRequired_of_intersection
    (h : s2253IntersectionIsBot) :
    s2216LinearDisjointnessRequired := by
  unfold s2216LinearDisjointnessRequired
  refine ⟨s2253Omega, inferInstance, inferInstance, inferInstance,
    s2253EmbedF, s2253EmbedL, ?_⟩
  exact (s2253LinearDisjointness_iff).mpr h
#print axioms s2253LinearDisjointness_iff
#print axioms s2253LinearDisjointnessRequired_of_intersection
end LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
end
