import tmp.sheaf.xif.paper.NativeCurvePointFieldsActual

/-!
# NativeCoverPointData: actual finite-etale stack cover and missing point projection

The actual source supply is

  T.clauseD.k_l_torsion_cover :
    SourceOrbicurveFiniteEtaleCover T.tuple.source.xK T.tuple.source.cK,

a genuine finite-etale cover of the native orbicurves (a stack morphism with a
finite-etale certificate).  It is NOT a point-set cover of the punctured curve:
SourceOrbicurveFiniteEtaleCover carries only map : source.Hom target and
finiteEtale, with no total-space carrier and no map to
T.arithmetic.curve's projective points.

This file records the actual stack cover, then keeps the point-set total-space
projection as an exact missing object.  The conditional NativeCoverPointData
constructor uses only explicit cover data; no arbitrary cover type or map is
chosen.

No PUnit/True/axiom/sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeCoverPointDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.NativeCurvePointFieldsActual
open LeanFormal.IUT.XiFPaper.NativeAssemblyCurveFieldsActual

universe w

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual finite-etale cover supplied by native clause D. -/
abbrev nativeKLtorsionCover :
    SourceOrbicurveFiniteEtaleCover T.tuple.source.xK T.tuple.source.cK :=
  T.clauseD.k_l_torsion_cover

/-- The actual finite-etale certificate of the native cover. -/
theorem nativeKLtorsionCover_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism (nativeKLtorsionCover (T := T)).map :=
  (nativeKLtorsionCover (T := T)).finiteEtale

/-- The actual stack map of the native cover. -/
def nativeKLtorsionCover_map :
    T.tuple.source.xK.Hom T.tuple.source.cK :=
  (nativeKLtorsionCover (T := T)).map

/-- Exact missing point-set total-space projection: a carrier over the punctured
projective point set with a surjective cover-to-punctured map. -/
structure NativeCoverTotalSpace where
  /-- The point-set total space of the finite-etale cover. -/
  cover : Type w
  /-- The projection from the cover total space to the punctured curve. -/
  coverToPunctured : cover -> nativePuncturedPoints (T := T)
  /-- The finite-etale cover is surjective on point sets. -/
  cover_surjective : Function.Surjective coverToPunctured

/-- The conditional NativeCoverPointData construction from the exact missing
total space. -/
noncomputable def nativeCoverPointDataOfTotalSpace
    (S : NativeCoverTotalSpace.{w} (T := T)) :
    NativeCoverPointData.{w} (T := T) where
  cover := S.cover
  coverToPunctured := S.coverToPunctured
  cover_surjective := S.cover_surjective

/-- The exact missing point-set total-space object. -/
def MissingNativeCoverTotalSpace : Prop :=
  Nonempty (NativeCoverTotalSpace.{w} (T := T))

end LeanFormal.IUT.XiFPaper.NativeCoverPointDataActual

end
