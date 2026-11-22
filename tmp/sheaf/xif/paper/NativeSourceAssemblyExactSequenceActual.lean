import tmp.sheaf.xif.paper.NativeSourceAssemblyActualFields
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual exact-sequence data and the exact missing splitting source

Clause D provides the actual profinite exact sequence of the native orbicurve
group data, with its injection, projection and exactness. It does not provide a
splitting section in the exact-sequence clause itself.

This file records the actual exact-sequence data and the exact missing source
object for a splitting section. The section carrier is a structure with an
actual group homomorphism and its right-inverse proof; no Classical.choice or
arbitrary section is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyExactSequenceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActualFields

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- Actual exact-sequence data from clause D. -/
structure ActualExactSequenceSource where
  inclusionInjective :
    Function.Injective X.S.clauseD.x_groups.sequence.inclusion
  projectionSurjective :
    Function.Surjective X.S.clauseD.x_groups.sequence.projection
  exactness :
    X.S.clauseD.x_groups.sequence.inclusion.hom.range =
      X.S.clauseD.x_groups.sequence.projection.hom.ker

/-- The actual exact-sequence data. -/
noncomputable def actualExactSequenceSource :
    ActualExactSequenceSource X where
  inclusionInjective := X.S.clauseD.x_groups.sequence.inclusion_injective
  projectionSurjective := X.S.clauseD.x_groups.sequence.projection_surjective
  exactness := X.S.clauseD.x_groups.sequence.exact

/-- Exact missing splitting section source object: an actual group section of
the clause-D projection with its right-inverse law. This is a source carrier,
not an arbitrarily chosen section. -/
structure ExactSequenceSplittingSource where
  sectionMap :
    ↥(Iut.AbsoluteGaloisProfinite X.S.arithmetic.K) →*
      ↥X.S.clauseD.x_groups.groups.arithmetic.group
  section_right_inverse : ∀ x : ↥(Iut.AbsoluteGaloisProfinite X.S.arithmetic.K),
    X.S.clauseD.x_groups.groups.projection (sectionMap x) = x

/-- Exact missing splitting source proposition. -/
def ExactSequenceSplittingSourceRequired : Prop :=
  Nonempty (ExactSequenceSplittingSource X)

/-- Projection: the section has the right-inverse law. -/
theorem ExactSequenceSplittingSource.right_inverse
    (S : ExactSequenceSplittingSource X) :
    ∀ x : ↥(Iut.AbsoluteGaloisProfinite X.S.arithmetic.K),
      X.S.clauseD.x_groups.groups.projection (S.sectionMap x) = x :=
  S.section_right_inverse

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyExactSequenceActual

end
