import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3109BaseQDescentAttempt

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- S3109 target: the exact base q descent package from the native F q. -/
def S3109BaseQDescentTarget : Prop :=
  Nonempty (BaseQDescentData (X := X))

/-- Actual constructor from an explicit descent map with the two q-candidate
laws. -/
noncomputable def S3109BaseQDescentOfMap
    (descent : NativeFCompletion (X := X) → NativeBaseCompletion (X := X))
    (hne : descent (nativeQActual X).q ≠ 0)
    (hval : (Valued.v (descent (nativeQActual X).q) :
      WithZero (Multiplicative Int)) < 1) :
    BaseQDescentData (X := X) where
  descent := descent
  q_ne_zero := hne
  valuation_lt_one := hval

/-- Base q candidate from a supplied descent package. -/
noncomputable def S3109BaseQCandidate
    (D : BaseQDescentData (X := X)) :
    FinitePlaceQCandidate (nativeBadBasePlace X) :=
  baseQCandidateOfDescent (X := X) D

@[simp] theorem S3109BaseQCandidate_q
    (D : BaseQDescentData (X := X)) :
    (S3109BaseQCandidate (X := X) D).q = D.descent (nativeQActual X).q := rfl

/-- Exact first missing object: the descent map itself. -/
def S3109MissingDescent : Prop :=
  Nonempty (BaseQDescentData (X := X))

#check S3109BaseQDescentTarget
#check S3109BaseQDescentOfMap
#check S3109BaseQCandidate
#check S3109BaseQCandidate_q
#check S3109MissingDescent

end LeanFormal.IUT.XiFPaper.S3109BaseQDescentAttempt
end