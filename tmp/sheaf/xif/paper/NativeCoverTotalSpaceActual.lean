import tmp.sheaf.xif.paper.NativeCoverPointDataActual

/-!
# NativeCoverTotalSpace: actual stack cover and missing point-set total space

Native clause D supplies the actual finite-etale stack cover

  nativeKLtorsionCover :
    SourceOrbicurveFiniteEtaleCover T.tuple.source.xK T.tuple.source.cK

with stack morphism and finite-etale certificate.  Its underlying object is an
etale stack fiber (a category-valued pseudofunctor), not a point-set total space
over the arithmetic punctured projective points T.arithmetic.curve.puncture.

The target NativeCoverTotalSpace requires

  cover : Type
  coverToPunctured : cover -> nativePuncturedPoints
  cover_surjective : Function.Surjective coverToPunctured.

No point functor from the stack cover total space to the arithmetic projective
points is present in SourceOrbicurveFiniteEtaleCover, T.arithmetic, or the
clause-D records.  The exact missing object is therefore the point-set total
space plus its projection.  This file records the actual stack cover and makes
no arbitrary choice of cover type or projection.

No PUnit/True/axiom/sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeCoverTotalSpaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.NativeCurvePointFieldsActual
open LeanFormal.IUT.XiFPaper.NativeCoverPointDataActual

universe w

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual finite-etale stack cover. -/
abbrev actualCover :
    SourceOrbicurveFiniteEtaleCover T.tuple.source.xK T.tuple.source.cK :=
  nativeKLtorsionCover (T := T)

/-- The actual cover stack morphism. -/
def actualCoverMap :
    T.tuple.source.xK.Hom T.tuple.source.cK :=
  (actualCover (T := T)).map

/-- The actual cover is finite etale. -/
theorem actualCover_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism (actualCoverMap (T := T)) :=
  (actualCover (T := T)).finiteEtale

/-- Exact missing point-set total-space projection: the carrier over the
punctured projective points, its projection, and surjectivity. -/
structure MissingCoverTotalSpace where
  cover : Type w
  coverToPunctured : cover -> nativePuncturedPoints (T := T)
  cover_surjective : Function.Surjective coverToPunctured

/-- The exact missing object, as a proposition. -/
def MissingNativeCoverTotalSpace : Prop :=
  Nonempty (MissingCoverTotalSpace.{w} (T := T))

/-- Conditional use: a supplied point-set total space gives the exact target
NativeCoverTotalSpace. -/
noncomputable def nativeCoverTotalSpaceOfData
    (S : MissingCoverTotalSpace.{w} (T := T)) :
    NativeCoverTotalSpace.{w} (T := T) where
  cover := S.cover
  coverToPunctured := S.coverToPunctured
  cover_surjective := S.cover_surjective

/-- The actual stack cover exists; the point-set total space/projection is
the exact missing object. -/
def ActualCoverPresent : Prop :=
  Nonempty (SourceOrbicurveFiniteEtaleCover
    T.tuple.source.xK T.tuple.source.cK)

theorem actualCoverPresent : ActualCoverPresent (T := T) :=
  ⟨actualCover (T := T)⟩

end LeanFormal.IUT.XiFPaper.NativeCoverTotalSpaceActual

end