import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import tmp.sheaf.n8.closure.NativeBadLiftActual
import LeanFormal.IUT.IUTI.InitialTheta.SplitReductionInput
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Minimal actual sufficient source condition for native split reduction

Clause B and the Tate comparison supply multiplicative reduction at every
native bad lift, but no general Tate-comparison-to-split theorem exists.
This file records the minimal actual sufficient condition:

at each bad lift, an actual finite-place split-reduction input consisting of a
q-candidate and a proof of split multiplicative reduction.

From that family the assembly's split field follows. No general split theorem
is asserted, and no arbitrary certificate is chosen.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeSplitSufficientConditionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual sufficient input at one native bad lift. -/
structure NativeSplitInputAt (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) where
  qCandidate : FinitePlaceQCandidate ((nativeBadLift T).lift b)
  splitReduction :
    T.arithmetic.curve.HasSplitMultiplicativeReductionAt
      ((nativeBadLift T).lift b)

/-- The minimal actual sufficient condition: one split input at every bad lift. -/
abbrev NativeSplitInputFamily : Type :=
  (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) → NativeSplitInputAt (l := l) T b

/-- A split-input family yields the assembly's split field. -/
theorem nativeSplitMultiplicativeAtLift_of_inputFamily
    (F : NativeSplitInputFamily T) :
    NativeSplitMultiplicativeAtLift T := by
  intro b
  exact (F b).splitReduction

/-- The actual q-candidates carried by the split-input family. -/
noncomputable def nativeSplitQCandidate
    (F : NativeSplitInputFamily T)
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    FinitePlaceQCandidate ((nativeBadLift T).lift b) :=
  (F b).qCandidate

/-- The actual split witnesses carried by the split-input family. -/
theorem nativeSplitQCandidate_split
    (F : NativeSplitInputFamily T)
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    T.arithmetic.curve.HasSplitMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :=
  (F b).splitReduction

/-- Consumer: the assembly's native reduction clause from the actual split-input
family and finite bad set. -/
noncomputable def nativeReductionClause_of_splitInputFamily
    [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]
    (F : NativeSplitInputFamily T) :
    Theorem311Source.SourceReductionClause
      (Selected (nativePlaceSelection T))
      (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :=
  nativeReductionClause T (nativeBadLift T)
    (nativeSplitMultiplicativeAtLift_of_inputFamily (l := l) T F)

/-- The actual concrete q split witness over the Gaussian concrete arithmetic
data: the split Tate curve at the concrete five-place. -/
noncomputable def concreteSplitReductionInput :
    InitialThetaSplitReductionInput l where
  arithmetic := concreteGaussianInitialThetaArithmeticData l
  place := concreteGaussianFivePlace
  qCandidate :=
    (concreteGaussianInitialThetaFinitePlaceInput l).qCandidate
  splitReduction :=
    concreteGaussianFivePlace_hasSplitMultiplicativeReduction l

/-- The concrete split input has the actual split reduction proof. -/
theorem concreteSplitReductionInput_split :
    (concreteSplitReductionInput (l := l)).arithmetic.curve.HasSplitMultiplicativeReductionAt
      (concreteSplitReductionInput (l := l)).place :=
  (concreteSplitReductionInput (l := l)).splitReduction

/-- The concrete split input gives an actual split witness, not a general-q
family. -/
theorem concreteSplitReductionInput_exists :
    Nonempty (InitialThetaSplitReductionInput.{0} l) :=
  ⟨concreteSplitReductionInput (l := l)⟩

end LeanFormal.IUT.XiFPaper.NativeSplitSufficientConditionActual

end
