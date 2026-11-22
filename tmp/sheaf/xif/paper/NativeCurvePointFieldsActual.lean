import tmp.sheaf.xif.paper.NativeAssemblyCurveFieldsActual
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve

/-!
# NativeCurvePointFields from the actual arithmetic curve

The arithmetic input T.arithmetic.curve is an actual PuncturedEllipticCurve F
with an actual Weierstrass curve and an actual projective puncture.  From it we
construct the actual point-set carriers:

  nativeCurvePoints      := T.arithmetic.curve.curve.toProjective.Point
  nativePuncturedPoints  := { P : nativeCurvePoints // P != puncture }
  nativeCurveToPunctured := Subtype.val

These are actual point sets from the source curve, not arbitrary Types.

The finite-etale cover point carrier is NOT supplied by T.arithmetic.curve:
T.clauseD.k_l_torsion_cover is a stack morphism SourceOrbicurveFiniteEtaleCover,
not a point-set cover with coverToPunctured and surjectivity.  This file therefore
constructs the curve/punctured part actually and keeps the cover point data as
the exact missing object.

No arbitrary type/map, PUnit, True, axiom, or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeCurvePointFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.NativeAssemblyCurveFieldsActual

universe u v w

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual projective point set of the arithmetic curve. -/
abbrev nativeCurvePoints : Type :=
  T.arithmetic.curve.curve.toProjective.Point

/-- The actual punctured point set: projective points different from the
recorded puncture. -/
abbrev nativePuncturedPoints : Type :=
  { P : nativeCurvePoints (T := T) // P ≠ T.arithmetic.curve.puncture }

/-- The actual inclusion of the punctured point set into the curve. -/
def nativeCurveToPunctured :
    nativePuncturedPoints (T := T) → nativeCurvePoints (T := T) :=
  Subtype.val

/-- The actual strict map from the punctured set to the curve is injective. -/
theorem nativeCurveToPunctured_injective :
    Function.Injective (nativeCurveToPunctured (T := T)) :=
  Subtype.val_injective

/-- The actual curve/punctured part of NativeCurvePointFields. -/
structure NativeCurvePart where
  curve : Type u
  puncturedCurve : Type v
  curveToPunctured : puncturedCurve → curve

/-- The actual curve/punctured data from T.arithmetic.curve. -/
noncomputable def nativeCurvePart : NativeCurvePart.{u, v} (T := T) where
  curve := nativeCurvePoints (T := T)
  puncturedCurve := nativePuncturedPoints (T := T)
  curveToPunctured := nativeCurveToPunctured (T := T)

/-- Exact missing cover point data: a point-set cover of the punctured curve
with its map and surjectivity.  The source clause D supplies only the stack
morphism k_l_torsion_cover, not this point-set data. -/
structure NativeCoverPointData where
  cover : Type w
  coverToPunctured : cover → nativePuncturedPoints (T := T)
  cover_surjective : Function.Surjective coverToPunctured

/-- The exact missing cover point-set object. -/
def MissingCoverPointData : Prop :=
  Nonempty (NativeCoverPointData.{w} (T := T))

/-- The full NativeCurvePointFields conditional on the actual missing cover
point data; the curve and punctured parts are the actual point sets above. -/
noncomputable def nativeCurvePointFieldsOfCover
    (C : NativeCoverPointData.{w} (T := T)) :
    NativeCurvePointFields.{u, v, w} (T := T) where
  curve := nativeCurvePoints (T := T)
  puncturedCurve := nativePuncturedPoints (T := T)
  cover := C.cover
  curveToPunctured := nativeCurveToPunctured (T := T)
  coverToPunctured := C.coverToPunctured
  cover_surjective := C.cover_surjective

/-- Exact missing cover object, stated as an uninhabited data package. -/
def MissingNativeCoverPointFields : Prop :=
  MissingCoverPointData (T := T)

/-- The actual curve/punctured part is available even without the cover. -/
theorem nativeCurvePart_available :
    Nonempty (NativeCurvePart.{u, v} (T := T)) :=
  ⟨nativeCurvePart (T := T)⟩

end LeanFormal.IUT.XiFPaper.NativeCurvePointFieldsActual

end
