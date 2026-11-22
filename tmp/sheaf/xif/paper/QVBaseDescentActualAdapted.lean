import tmp.sheaf.xif.paper.QPilotFTimesMuPrimeStripActualAdapted
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.Foundations.NumberField.LocalQParameterExtension

/-!
# Actual base q descent: inverse of completionMap on its range

IUT III, Definition 3.8, (i), pp. 112-113: q-pilot data are indexed by
q_v for v in V_bad; the base q_v live at the base Fmod places, while clause B
supplies q candidates at finite F-places above them.

The completion map

  completionMap : Completion (comap p) -> Completion p

is an actual base-to-extension ring embedding (FinitePlaceExtension.lean,
completionMap/completionMap_injective).  It has no field-theoretic inverse on
the whole extension completion.  On its actual range, however, it has a genuine
inverse: choose the unique preimage.  This file constructs that inverse as an
actual map and uses it for the V_bad-indexed base q descent.

The remaining minimal exact input is QVBasePreimageData: for each bad place b,
a base q candidate at comap(lift b) together with the equality that its
completionMap image is the actual clause-B q_v at the F-lift.  No such equality
is fabricated; it is the exact base q identification.

No inequality is asserted as a theorem.  The q-candidate laws are carried as
the actual fields of FinitePlaceQCandidate.  No toy/True/PUnit/axiom/sorry.
WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QVBaseDescentActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual inverse of the completion map on its range: the unique
preimage of a point in the range. -/
noncomputable def completionDescentOnRange
    {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (place : NumberField.FinitePlace K)
    (x : Set.range (completionMap (k := k) place)) :
    (NumberFieldFinitePlace.comap (k := k) place).maximalIdeal.adicCompletion k :=
  Classical.choose x.2

/-- The constructed inverse is a genuine section of completionMap on its
range. -/
theorem completionMap_completionDescentOnRange
    {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (place : NumberField.FinitePlace K)
    (x : Set.range (completionMap (k := k) place)) :
    completionMap (k := k) place
        (completionDescentOnRange (k := k) place x) = x.1 :=
  Classical.choose_spec x.2

/-- The actual base q preimage datum at a bad place b: a q candidate at the
contracted base Fmod place, whose completionMap image is the actual clause-B q_v
at the F-lift.  This is the minimal exact base q identification; the descent at
the level of the completion range is constructed below. -/
structure QVBasePreimageData
    (b : Bad (nativePlaceSelection T)) where
  baseQ : FinitePlaceQCandidate
    (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b))
  q_eq : completionMap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b)
      (baseQ.q : ((NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b)).maximalIdeal.adicCompletion T.arithmetic.Fmod)) =
    (qVFamily T b).q

/-- The actual V_bad-indexed base q descent family: the inverse completion map
on its range, together with the actual base q preimage data. -/
structure QVBaseDescentFamily where
  preimage : (b : Bad (nativePlaceSelection T)) → QVBasePreimageData T b
  descent : (b : Bad (nativePlaceSelection T)) →
    Set.range (completionMap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b)) →
      (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b)).maximalIdeal.adicCompletion T.arithmetic.Fmod
  descent_spec : (b : Bad (nativePlaceSelection T))
      (x : Set.range (completionMap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b))) →
    completionMap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b) (descent b x) = x.1

/-- Actual construction of QVBaseDescentFamily from the minimal preimage data:
the descent is the inverse completionMap on its range. -/
noncomputable def qVBaseDescentFamilyOfPreimage
    (P : (b : Bad (nativePlaceSelection T)) → QVBasePreimageData T b) :
    QVBaseDescentFamily T where
  preimage := P
  descent := fun b x =>
    completionDescentOnRange (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b) x
  descent_spec := fun b x =>
    completionMap_completionDescentOnRange (k := T.arithmetic.Fmod)
      ((nativeBadLift T).lift b) x

/-- The actual base q family obtained from the preimage data. -/
def qVBaseFamilyOfPreimage
    (P : (b : Bad (nativePlaceSelection T)) → QVBasePreimageData T b)
    (b : Bad (nativePlaceSelection T)) :
    FinitePlaceQCandidate
      (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b)) :=
  (P b).baseQ

/-- The base q family is the completionMap image prescribed by the preimage
data. -/
theorem qVBaseFamilyOfPreimage_q_eq
    (P : (b : Bad (nativePlaceSelection T)) → QVBasePreimageData T b)
    (b : Bad (nativePlaceSelection T)) :
    completionMap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b)
        ((qVBaseFamilyOfPreimage T P b).q :
          ((NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
            ((nativeBadLift T).lift b)).maximalIdeal.adicCompletion T.arithmetic.Fmod)) =
      (qVFamily T b).q :=
  (P b).q_eq

/-- The actual descent family's range section is exactly the inverse
completionMap. -/
theorem qVBaseDescentFamilyOfPreimage_descent_spec
    (P : (b : Bad (nativePlaceSelection T)) → QVBasePreimageData T b)
    (b : Bad (nativePlaceSelection T))
    (x : Set.range (completionMap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b))) :
    completionMap (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b)
        ((qVBaseDescentFamilyOfPreimage T P).descent b x) = x.1 :=
  (qVBaseDescentFamilyOfPreimage T P).descent_spec b x

end LeanFormal.IUT.XiFPaper.QVBaseDescentActualAdapted
