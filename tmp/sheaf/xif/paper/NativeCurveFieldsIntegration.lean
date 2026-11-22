import tmp.sheaf.xif.paper.NativeCurvePointFieldsActual
import tmp.sheaf.xif.paper.NativeCoverTotalSpaceActual

/-!
# Integration: actual stack cover -> NativeCurvePointFields

This integration layer wires the actual clause-D stack cover and the exact
missing point-set total space into the NativeCurvePointFields package.

Actual:
* nativeCurvePoints, nativePuncturedPoints, nativeCurveToPunctured from
  T.arithmetic.curve (NativeCurvePointFieldsActual);
* actualCover : SourceOrbicurveFiniteEtaleCover ... (NativeCoverTotalSpaceActual).

Missing:
* MissingCoverTotalSpace: cover carrier + coverToPunctured + surjectivity.

The conditional constructor below produces NativeCurvePointFields from the
missing total space plus the actual curve/punctured point sets.  No cover type
or map is fabricated.

No PUnit/True/axiom/sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeCurveFieldsIntegration

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.NativeCurvePointFieldsActual
open LeanFormal.IUT.XiFPaper.NativeCoverTotalSpaceActual

universe w

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual stack cover integrated from the clause-D record. -/
abbrev integratedStackCover :
    SourceOrbicurveFiniteEtaleCover T.tuple.source.xK T.tuple.source.cK :=
  actualCover (T := T)

/-- The actual finite-etale certificate of the integrated stack cover. -/
theorem integratedStackCover_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism (integratedStackCover (T := T)).map :=
  actualCover_finiteEtale (T := T)

/-- Conversion from the exact missing total space to the cover-point data used
by NativeCurvePointFields. -/
noncomputable def nativeCoverPointDataOfMissing
    (S : MissingCoverTotalSpace.{w} (T := T)) :
    NativeCoverPointData.{w} (T := T) where
  cover := S.cover
  coverToPunctured := S.coverToPunctured
  cover_surjective := S.cover_surjective

/-- Integrated NativeCurvePointFields: actual curve/punctured points plus the
supplied missing cover total space. -/
noncomputable def integratedCurvePointFields
    (S : MissingCoverTotalSpace.{w} (T := T)) :
    NativeCurvePointFields.{0, 0, w} (T := T) :=
  nativeCurvePointFieldsOfCover (T := T)
    (nativeCoverPointDataOfMissing (T := T) S)

/-- The actual curve/punctured part remains available unconditionally. -/
theorem integratedCurvePart_available :
    Nonempty (NativeCurvePart.{0, 0} (T := T)) :=
  nativeCurvePart_available (T := T)

/-- The exact missing integration field, recorded at this layer. -/
def MissingCurveCoverIntegration : Prop :=
  MissingNativeCoverTotalSpace (T := T)

/-- The integration missing object is exactly the missing point-set total space;
no stronger cover object is introduced. -/
theorem missingCurveCoverIntegration_iff :
    MissingCurveCoverIntegration (T := T) ↔
      MissingNativeCoverTotalSpace (T := T) :=
  Iff.rfl

/-- If the missing total space is supplied, the integrated NativeCurvePointFields
exists. -/
theorem integratedCurvePointFields_nonempty_of_missing
    (h : MissingCurveCoverIntegration (T := T)) :
    Nonempty (NativeCurvePointFields.{0, 0, w} (T := T)) := by
  rcases h with ⟨S⟩
  exact ⟨integratedCurvePointFields (T := T) S⟩

#check actualCover
#check MissingNativeCoverTotalSpace
#check nativeCurvePoints
#check nativePuncturedPoints
#check nativeCurveToPunctured
#check nativeCurvePointFieldsOfCover
#check integratedCurvePointFields

end LeanFormal.IUT.XiFPaper.NativeCurveFieldsIntegration

end
