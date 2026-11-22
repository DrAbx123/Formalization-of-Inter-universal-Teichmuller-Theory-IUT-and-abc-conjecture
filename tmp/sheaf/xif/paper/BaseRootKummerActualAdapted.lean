import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.xif.paper.C3DonorUnconditionalActual
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.n8.closure.NativeC3

/-!
# BaseRootKummerData from native roots/Kummer: exact missing transport

The native root and Kummer data are actual:

  nativeRootSystemActual
    : NatRootSystem (unitToAlgClosed
        (candidateUnits (nativeFPlaceOverBad X) (nativeQActual X)))

  nativeKummerClassActual
    : CyclotomicTower (AlgebraicClosure (Completion (nativeFPlaceOverBad X))).

The C3 donor needs, at the base Fmod place nativeC3Place X and a base q,

  roots : NatRootSystem (candidateUnits (nativeC3Place X) baseQ)
  roots' : NatRootSystem (candidateUnits (nativeC3Place X) baseQ)
  kummerClass : CyclotomicTower (CommonPrimeCompletion ...).

The carrier mismatch is the exact obstruction: native roots live in the
algebraic closure of the F-completion, while donor roots live in the base
completion itself. The canonical map goes base completion -> F completion ->
algebraic closure, not back; and no identification of the native q with the
base q exists. Therefore no base root/Kummer data is constructed from the
native data. The exact missing object is isolated as
ExactMissingBaseRootKummer; no roots, Kummer class, or transport are invented.

No fake data, forbidden placeholder, axiom, or unfilled proof is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseRootKummerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual native root system over the F-completion q. -/
noncomputable def nativeRootSystemActual :
    NatRootSystem
      (unitToAlgClosed
        (candidateUnits (K := X.S.arithmetic.Fmod)
          (nativeFPlaceOverBad X) (nativeQActual X))) :=
  qCandidateRootSystem (nativeFPlaceOverBad X) (nativeQActual X)

/-- The actual native Kummer class tower. -/
noncomputable def nativeKummerClassActual :
    CyclotomicTower
      (AlgebraicClosure (Completion (nativeFPlaceOverBad X))) :=
  nativeKummerClass X (nativeQDonorActual X)

/-- The conditional base q from the exact descent package. -/
noncomputable def baseQCandidate (D : BaseQDescentData (X := X)) :
    FinitePlaceQCandidate (nativeC3Place X).val :=
  baseQCandidateOfDescent (X := X) D

/-- The base q unit in the base completion. -/
noncomputable def baseQUnit (D : BaseQDescentData (X := X)) :
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))ˣ :=
  candidateUnits (K := X.S.arithmetic.Fmod) (nativeC3Place X)
    (baseQCandidate (X := X) D)

/-- Exact missing transport: base-completion root systems over the base q unit,
not algebraic-closure roots of the F-completion. -/
structure ExactMissingBaseRootKummer
    (D : BaseQDescentData (X := X)) : Prop where
  roots : NatRootSystem (baseQUnit (X := X) D)
  roots' : NatRootSystem (baseQUnit (X := X) D)
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- The exact missing object is a base root/Kummer package over the conditional
base q, not a transport of the F-completion algebraic-closure roots. -/
def BaseRootKummerMissing
    (D : BaseQDescentData (X := X)) : Prop :=
  Nonempty (ExactMissingBaseRootKummer (X := X) D)

/-- The native roots' value lives in the algebraic closure of the F-completion;
this is the exact type that cannot be identified with the base-completion q
unit used by the donor. -/
theorem nativeRootSystemActual_value_type :
    NatRootSystem
      (unitToAlgClosed
        (candidateUnits (K := X.S.arithmetic.Fmod)
          (nativeFPlaceOverBad X) (nativeQActual X))) :=
  nativeRootSystemActual (X := X)

end LeanFormal.IUT.XiFPaper.BaseRootKummerActualAdapted

end
