import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# ETA-3: actual etaQ q-side data

Constructs the actual q-side data from native Clause (b) q/Tate/qUnit and the
actual value-group scalar.  The Rval -> Rss q-side map is the missing
production declaration; it is recorded as an exact named gap.  No direct scalar
comparison between Q and any other real is asserted.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.IUTII.Frobenioid.Example36

namespace LeanFormal.IUT.N8Closure.EtaQActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual Rval carrier: units of the native F-completion at the selected bad
finite place (the q/Tate carrier). -/
abbrev Rval (X : N8NativeInput l) : Type _ :=
  (Completion (nativeFPlaceOverBad X))ˣ

/-- Actual base finite prime underlying the native bad base place. -/
noncomputable def etaQBasePrime :
    HeightOneSpectrum (𝓞 X.S.arithmetic.Fmod) :=
  NumberFieldFinitePlace.underlyingPrime (nativeBadBasePlace X)

/-- Actual Rss carrier: the value-group-level local value monoid at the native
base finite prime. -/
abbrev Rss (X : N8NativeInput l) : Type _ :=
  finitePlaceUnitValueMonoid (F := X.S.arithmetic.Fmod) (etaQBasePrime X)

/-- Actual native q-unit from the Clause (b) Tate comparison. -/
noncomputable def etaQUnit (X : N8NativeInput l) : Rval X :=
  nativeQUnitActual (X := X)

/-- Actual value-group scalar of the native q-unit: the unit norm log degree
at the native F-completion. -/
noncomputable def etaQScalar : ℝ :=
  Multiplicative.toAdd
    (unitNormLogDegree (Completion (nativeFPlaceOverBad X)) (etaQUnit (X := X)))

theorem etaQScalar_eq_unitNormLogDegree (X : N8NativeInput l) :
    etaQScalar X = Multiplicative.toAdd
      (unitNormLogDegree (Completion (nativeFPlaceOverBad X))
        (nativeQUnitActual (X := X))) := rfl

/-- Exact missing Rval -> Rss q-side map.  The map is data, not a scalar
comparison; its source image is the actual q-unit image. -/
structure RvalToRssQMap (X : N8NativeInput l) where
  toRss : Rval X → Rss X
  qImage : Rss X
  qImage_eq : toRss (etaQUnit X) = qImage

/-- Actual q-side etaQ data.  The Rval -> Rss map is an input; no direct
scalar comparison is part of the structure. -/
structure EtaQActualData (X : N8NativeInput l) where
  qUnit : Rval X
  qScalar : ℝ
  qScalar_eq : qScalar = etaQScalar X
  rvalToRss : RvalToRssQMap X

def etaQActualData_of_map
    (X : N8NativeInput l) (M : RvalToRssQMap X) :
    EtaQActualData X :=
  ⟨etaQUnit X, etaQScalar X, rfl, M⟩

end LeanFormal.IUT.N8Closure.EtaQActual

end