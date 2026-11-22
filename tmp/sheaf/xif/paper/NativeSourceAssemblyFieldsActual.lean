import tmp.sheaf.xif.paper.NativeSourceAssemblyActual
import tmp.sheaf.n8.closure.NativeOrbicurveCarriersActual
import tmp.sheaf.n8.closure.NativeSourceOrbicurveActual
import tmp.sheaf.n8.closure.NativeOrbicurveCountProof

/-!
# Actual NativeSourceAssembly carrier fields and exact-sequence gap

Builds the carrier part of NativeSourceAssembly from actual clause-D/E data:
* curve/puncturedCurve/cover are the actual finite-etale-cover carrier;
* the two point maps are the actual identity maps with surjectivity;
* structureGroup is the actual x-arithmetic profinite group.

The exactSequence field is constructed from the actual clause-D profinite
exact sequence only when the missing splitting section is supplied.
The remaining NativeSourceAssembly fields (badFinite, split, torsionGaps,
cuspCount, d7, cuspHyp, compatibility fields) are not constructed here and
are reported exactly. No toy/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeOrbicurveCarriersActual
open LeanFormal.IUT.InitialThetaSource.NativeSourceOrbicurveActual
open LeanFormal.IUT.InitialThetaSource.NativeOrbicurveCountProof
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Actual carrier fields from the finite-etale-cover carrier. -/
structure ActualNativeAssemblyCarrierFields where
  curve : Type (u + 1)
  puncturedCurve : Type (u + 1)
  cover : Type (u + 1)
  structureGroup : Type
  [structureGroupLaw : Group structureGroup]
  curveToPunctured : puncturedCurve -> curve
  coverToPunctured : cover -> puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured

/-- The actual carrier fields from clause D. -/
noncomputable def actualNativeAssemblyCarrierFields :
    ActualNativeAssemblyCarrierFields where
  curve := NativeCoverCarrier T.tuple.source
  puncturedCurve := PuncturedCurveCarrier T.tuple.source
  cover := CoverCarrier T.tuple.source
  structureGroup := StructureGroupCarrier T.clauseD
  structureGroupLaw := structureGroup_actual_group T.clauseD
  curveToPunctured := curveToPunctured T.tuple.source
  coverToPunctured := coverToPunctured T.tuple.source
  cover_surjective := coverToPunctured_surjective T.tuple.source

/-- The actual curve-compatibility proposition/witness from clause D. -/
theorem actualCurveCompatibility :
    Nonempty (NativeCoverCarrier T.tuple.source) :=
  LeanFormal.IUT.InitialThetaSource.NativeOrbicurveCarriersActual.curveCompatibility_of_clauseD T.clauseD

/-- The exact missing splitting section for the actual clause-D profinite
exact sequence. -/
def MissingExactSequenceSplittingSection : Prop :=
  ExactSequenceSplittingPrimitive T.clauseD

/-- Conditional construction of the actual SourceExactSequenceClause from
the actual clause-D sequence and the missing splitting section. -/
noncomputable def actualSourceExactSequence
    (h : MissingExactSequenceSplittingSection (l := l) T) :
    SourceExactSequenceClause :=
  sourceExactSequenceOfGroups T.clauseD.x_groups.sequence
    (Classical.choose h) (Classical.choose_spec h)

/- Exact remaining NativeSourceAssembly fields: badFinite, split,
torsionGaps, exactSequence (missing splitting section above), cuspCount and
positivity, d7, cuspHyp, and the five compatibility propositions/proofs.
The carrier fields and curve-compatibility witness are actual. -/

#check ActualNativeAssemblyCarrierFields
#check actualNativeAssemblyCarrierFields
#check actualCurveCompatibility
#check MissingExactSequenceSplittingSection
#check actualSourceExactSequence

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFieldsActual

end
