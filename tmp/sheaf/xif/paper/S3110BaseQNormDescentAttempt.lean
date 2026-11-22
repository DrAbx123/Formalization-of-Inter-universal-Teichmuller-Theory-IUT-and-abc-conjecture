import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Valued
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3110BaseQNormDescentAttempt

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The norm descent from the F-completion to the Fmod-completion, using the
actual completion algebra. -/
noncomputable def S3110NormDescent :
    NativeFCompletion (X := X) → NativeBaseCompletion (X := X) := by
  intro x
  letI : Algebra
      ((comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.adicCompletion
        X.S.arithmetic.Fmod)
      ((nativeFPlaceOverBad X).maximalIdeal.adicCompletion X.S.arithmetic.F) :=
    completionAlgebra (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)
  let z : (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.adicCompletion
      X.S.arithmetic.Fmod :=
    Algebra.norm
      ((comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.adicCompletion
        X.S.arithmetic.Fmod) x
  have hbase : (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.adicCompletion
      X.S.arithmetic.Fmod = NativeBaseCompletion (X := X) := by
    rw [nativeFPlaceOverBad_comap X]
  exact hbase ▸ z

/-- The base q obtained by applying the norm descent to the native q. -/
noncomputable def S3110BaseQ : NativeBaseCompletion (X := X) :=
  S3110NormDescent (X := X) (nativeQActual X).q


/-- S3110 target: the norm-descent package with the q-candidate laws. -/
def S3110BaseQNormDescentTarget : Prop :=
  Nonempty (BaseQDescentData (X := X))

/-- Conditional closure from the two q-candidate laws. -/
theorem S3110_baseQDescent_of_laws
    (hne : S3110BaseQ (X := X) ≠ 0)
    (hval : (Valued.v (S3110BaseQ (X := X)) :
      WithZero (Multiplicative Int)) < 1) :
    S3110BaseQNormDescentTarget (X := X) :=
  ⟨{ descent := S3110NormDescent (X := X)
     q_ne_zero := hne
     valuation_lt_one := hval }⟩

#check S3110NormDescent
#check S3110BaseQ
#check S3110BaseQNormDescentTarget
#check S3110_baseQDescent_of_laws

end LeanFormal.IUT.XiFPaper.S3110BaseQNormDescentAttempt
end