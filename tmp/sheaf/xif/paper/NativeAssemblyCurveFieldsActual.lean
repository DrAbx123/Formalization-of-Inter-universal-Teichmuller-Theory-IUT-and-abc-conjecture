import tmp.sheaf.xif.paper.NativeSourceAssemblyActual
import tmp.sheaf.xif.paper.NativeSourceOrbicurveActual

/-!
# NativeSourceAssembly curve/exactSequence fields: actual construction attempt

The frozen NativeSourceAssembly requires

  exactSequence : SourceExactSequenceClause
  curve, puncturedCurve, cover, structureGroup : Type
  [Group structureGroup]
  curveToPunctured, coverToPunctured, cover_surjective.

Actual source data available:

* the native clause-D profinite exact sequence
  T.clauseD.x_groups.sequence (actual ProfiniteFundamentalExactSequence);
* the actual native structure group
  ↥T.clauseD.x_groups.sequence.arithmetic;
* the actual native orbicurve/cover stack records
  T.clauseD.k_l_torsion_cover and the group data.

What is missing:

1. a splitting section Galois -> arithmetic with its right-inverse law; the
   SourceExactSequenceClause needs it, and the native exact sequence does not
   carry it;
2. point-set carriers curve/puncturedCurve/cover and their two maps; the source
   clause carries stack morphisms, not point-set maps;
3. the curve-compatibility/cusp data (handled by other fields of
   NativeSourceAssembly, not here).

This file constructs the actual native structureGroup and the exactSequence
conditionally from the exact source splitting section, and packages the
remaining explicit point-set data.  No arbitrary map, PUnit, True, axiom, or
sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeAssemblyCurveFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeSourceAssemblyActual
open LeanFormal.IUT.InitialThetaSource.NativeSourceOrbicurveActual

universe u v w

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual native structure group from the clause-D exact sequence. -/
abbrev nativeStructureGroup : Type :=
  ↥T.clauseD.x_groups.sequence.arithmetic

instance nativeStructureGroupGroup : Group (nativeStructureGroup T) :=
  inferInstance

/-- The actual native exact sequence, conditional on the missing splitting
section and its right-inverse law. -/
noncomputable def nativeExactSequence
    (sectionMap : ↥T.clauseD.x_groups.sequence.galois →*
      ↥T.clauseD.x_groups.sequence.arithmetic)
    (section_right_inverse : forall x,
      T.clauseD.x_groups.sequence.projection (sectionMap x) = x) :
    SourceExactSequenceClause.{u, v, w} :=
  sourceExactSequenceOfGroups
    (sequence := T.clauseD.x_groups.sequence)
    sectionMap section_right_inverse

/-- Exact missing splitting-section object for the native exact sequence. -/
def MissingExactSequenceSection : Prop :=
  Nonempty { sectionMap : ↥T.clauseD.x_groups.sequence.galois →*
      ↥T.clauseD.x_groups.sequence.arithmetic //
    forall x, T.clauseD.x_groups.sequence.projection (sectionMap x) = x }

/-- Explicit point-set curve/cover data required by NativeSourceAssembly.
These are the actual missing point carriers when only the source stack morphism
T.clauseD.k_l_torsion_cover is available. -/
structure NativeCurvePointFields where
  curve : Type u
  puncturedCurve : Type v
  cover : Type w
  curveToPunctured : puncturedCurve -> curve
  coverToPunctured : cover -> puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured

/-- The exact conditional curve/exactSequence field package. -/
structure NativeAssemblyCurveFields where
  exactSequence : SourceExactSequenceClause.{u, v, w}
  structureGroup : Type u
  [structureGroupLaw : Group structureGroup]
  curve : Type u
  puncturedCurve : Type v
  cover : Type w
  curveToPunctured : puncturedCurve -> curve
  coverToPunctured : cover -> puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured

/-- Construct the exact conditional field package from the actual native
structure group, an explicit splitting section, and the missing point-set
carriers. -/
noncomputable def nativeAssemblyCurveFieldsOfSource
    (sectionMap : ↥T.clauseD.x_groups.sequence.galois →*
      ↥T.clauseD.x_groups.sequence.arithmetic)
    (section_right_inverse : forall x,
      T.clauseD.x_groups.sequence.projection (sectionMap x) = x)
    (C : NativeCurvePointFields.{u, v, w}) :
    NativeAssemblyCurveFields.{u, v, w} (T := T) where
  exactSequence := nativeExactSequence (T := T) sectionMap section_right_inverse
  structureGroup := nativeStructureGroup T
  structureGroupLaw := inferInstance
  curve := C.curve
  puncturedCurve := C.puncturedCurve
  cover := C.cover
  curveToPunctured := C.curveToPunctured
  coverToPunctured := C.coverToPunctured
  cover_surjective := C.cover_surjective

/-- The exact missing point-set data: the actual source cover record supplies a
stack morphism and finite-etale proof, not point-set curve/cover carriers and
their maps. -/
def MissingCurvePointFields : Prop :=
  Nonempty (NativeCurvePointFields.{u, v, w})

end LeanFormal.IUT.XiFPaper.NativeAssemblyCurveFieldsActual

end