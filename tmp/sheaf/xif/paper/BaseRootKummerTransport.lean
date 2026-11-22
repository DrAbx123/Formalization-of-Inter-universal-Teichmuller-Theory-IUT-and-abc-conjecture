import tmp.sheaf.xif.paper.BaseRootKummerActual
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.n8.closure.NativeC3

/-!
# Base root/Kummer transport: type-level obstruction

Native root data is an algebraic-closure object:

  nativeRootSystemActual
    : NatRootSystem (unitToAlgClosed
        (candidateUnits (nativeFPlaceOverBad X) (nativeQActual X))).

The C3 donor root field is a completion object:

  roots : NatRootSystem (candidateUnits (nativeC3Place X) baseQ).

There is no map from the algebraic closure of the F-completion back to the base
completion, and no identification of nativeQActual with a base q. Thus the
native roots cannot be transported into a NatRootSystem over
candidateUnits (nativeC3Place X) baseQ: the root values live in different
monoids.

The same carrier mismatch holds for the Kummer towers: the native tower is over
AlgebraicClosure (Completion (nativeFPlaceOverBad X)), while the donor tower is
over CommonPrimeCompletion (nativeC3Place X).

This file therefore constructs no BaseRootKummerData. It records the exact
type-level obstruction and the exact missing object. No root, Kummer class,
transport map, toy data, forbidden placeholder, axiom, or unfilled proof is
introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseRootKummerTransport

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.XiFPaper.BaseRootKummerActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The native root system is over the algebraic closure of the F-completion. -/
abbrev NativeAlgRootCarrier : Type :=
  (AlgebraicClosure (Completion (nativeFPlaceOverBad X)))ˣ

/-- The native root system is an algebraic-closure root system. -/
noncomputable def nativeRootsInAlgClosure :
    NatRootSystem
      (unitToAlgClosed
        (candidateUnits (K := X.S.arithmetic.Fmod)
          (nativeFPlaceOverBad X) (nativeQActual X))) :=
  nativeRootSystemActual (X := X)

/-- The base q unit (conditional on the exact base q descent). -/
noncomputable def baseQUnit (D : BaseQDescentData (X := X)) :
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))ˣ :=
  candidateUnits (K := X.S.arithmetic.Fmod) (nativeC3Place X)
    (baseQCandidate (X := X) D)

/-- Exact missing transport object: base-completion roots/Kummer data, not a
map from the F-completion algebraic closure. -/
structure MissingBaseRootKummerTransport
    (D : BaseQDescentData (X := X)) : Prop where
  roots : NatRootSystem (baseQUnit (X := X) D)
  roots' : NatRootSystem (baseQUnit (X := X) D)
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- No transport from native algebraic-closure roots to base-completion roots
is supplied. The exact missing object is the base root/Kummer data. -/
def BaseRootKummerTransportMissing
    (D : BaseQDescentData (X := X)) : Prop :=
  Nonempty (MissingBaseRootKummerTransport (X := X) D)

/-- The native root value carrier is the F-completion algebraic closure. -/
theorem nativeRootValueCarrier :
    NatRootSystem
      (unitToAlgClosed
        (candidateUnits (K := X.S.arithmetic.Fmod)
          (nativeFPlaceOverBad X) (nativeQActual X))) :=
  nativeRootsInAlgClosure (X := X)

end LeanFormal.IUT.XiFPaper.BaseRootKummerTransport

end
