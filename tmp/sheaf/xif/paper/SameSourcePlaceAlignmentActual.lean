import tmp.sheaf.xif.paper.ActualC3DonorFromNative
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.n8.closure.NativeC3

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Same-source place alignment: native bad places, C3 tensor places, theta values

This file works entirely inside the native source X (whose S is the native
initial-Theta datum). It does not compare I.initial.arithmetic.Fmod with
X.S.arithmetic.Fmod and constructs no cross-source base-field equivalence.

Actual data:
* each bad place b is the base Fmod place b.1;
* each native C3 tensor index i has the base Fmod place
  L.tensorPlaces i (L.tensorTuple i), coerced to a NumberField.FinitePlace;
* the native tensor donor L is the actual explicit native tensor data;
* theta values are the actual source-theater theta packet values, q = 1/5.

The same-source comparison relation is the actual equality of these base
places. Its fibers and the theta-value map are actual; the statement that every
bad place has an aligned C3 tensor index is recorded as an exact proposition,
not asserted.

No cross-source base-field comparison, True/PUnit, empty type, axiom, or sorry
is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.SameSourcePlaceAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ActualC3DonorFromNative
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual base Fmod place of a native bad place. -/
noncomputable def sameSourceBadPlace
    (b : Bad (nativePlaceSelection X.S)) :
    NumberField.FinitePlace X.S.arithmetic.Fmod :=
  b.1

/-- The actual base Fmod place of a native C3 tensor index. -/
noncomputable def sameSourceC3Place
    (L : NativeTensorLandingDonor X) (i : L.tensorIndex) :
    NumberField.FinitePlace X.S.arithmetic.Fmod :=
  (L.tensorPlaces i (L.tensorTuple i) : NumberField.FinitePlace
    X.S.arithmetic.Fmod)

/-- The actual same-source place-alignment relation. -/
def sameSourcePlaceAligned
    (L : NativeTensorLandingDonor X)
    (b : Bad (nativePlaceSelection X.S)) (i : L.tensorIndex) : Prop :=
  sameSourceC3Place X L i = sameSourceBadPlace X b

/-- The actual C3 tensor indices aligned with a bad place. -/
def sameSourceAlignedIndices
    (L : NativeTensorLandingDonor X)
    (b : Bad (nativePlaceSelection X.S)) : Set L.tensorIndex :=
  {i | sameSourcePlaceAligned X L b i}

/-- The actual theta value at a signed label, from the source-theater theta
packet (q = 1/5). -/
noncomputable def sameSourceThetaValue (j : SignedLabel l.value) : Real :=
  (sourceTheaterThetaPacket (l := l)).scale j

/-- The actual theta-value family over the native bad places. -/
noncomputable def sameSourceThetaAt
    (b : Bad (nativePlaceSelection X.S)) (j : SignedLabel l.value) : Real :=
  sameSourceThetaValue (l := l) j

/-- The pair set of actual bad place/C3 index alignments. -/
def sameSourceAlignmentPairs
    (L : NativeTensorLandingDonor X) :
    Set (Bad (nativePlaceSelection X.S) × L.tensorIndex) :=
  {p | sameSourcePlaceAligned X L p.1 p.2}

/-- The actual source comparison data: both place maps, the theta-value family,
and the exact alignment proposition. -/
structure SameSourcePlaceComparisonData
    (L : NativeTensorLandingDonor X) where
  badPlace : Bad (nativePlaceSelection X.S) → NumberField.FinitePlace
    X.S.arithmetic.Fmod
  c3Place : L.tensorIndex → NumberField.FinitePlace X.S.arithmetic.Fmod
  thetaAt : Bad (nativePlaceSelection X.S) → SignedLabel l.value → Real
  alignment : Prop

/-- The actual comparison data: exact place maps and theta values; alignment is
the exact proposition that every bad place has an aligned C3 tensor index. -/
noncomputable def sameSourcePlaceComparisonData
    (L : NativeTensorLandingDonor X) :
    SameSourcePlaceComparisonData (l := l) X L where
  badPlace := sameSourceBadPlace X
  c3Place := sameSourceC3Place X L
  thetaAt := sameSourceThetaAt X
  alignment := ∀ b, (sameSourceAlignedIndices X L b).Nonempty

/-- The exact obstruction: every bad place has an aligned C3 tensor index. This
is the alignment proposition of the comparison data; it is not asserted. -/
def SameSourceAlignmentObstruction
    (L : NativeTensorLandingDonor X) : Prop :=
  ∀ b, (sameSourceAlignedIndices X L b).Nonempty

/-- The actual alignment relation is exactly equality of the two same-source
base places. -/
theorem sameSourcePlaceAligned_iff
    (L : NativeTensorLandingDonor X)
    (b : Bad (nativePlaceSelection X.S)) (i : L.tensorIndex) :
    sameSourcePlaceAligned X L b i ↔
      sameSourceC3Place X L i = sameSourceBadPlace X b :=
  Iff.rfl

/-- The theta-value family is the actual source-theater theta packet scale. -/
theorem sameSourceThetaAt_apply
    (b : Bad (nativePlaceSelection X.S)) (j : SignedLabel l.value) :
    sameSourceThetaAt X b j = (sourceTheaterThetaPacket (l := l)).scale j :=
  rfl

end LeanFormal.IUT.XiFPaper.SameSourcePlaceAlignmentActual

end
