import Iut.Foundations.SourceFiniteStageModelFrobenioid
import Iut.Foundations.SourceFrobenioidRationalMonoidTransport
import tmp.sheaf.xif.paper.S357OtrianglerightStructuralSheafActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S369OtriSplitFrobenioidActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S357OtrianglerightStructuralSheafActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual native bad completion place. -/
abbrev nativeStagePlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- 1a. The actual stage-model Frobenioid presentation at the native bad place.
This is the repo's SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation,
not a fabricated Frobenioid. -/
noncomputable def nativeStageFrobenioidPresentation :
    Iut.FrobenioidPresentation :=
  Iut.SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
    (K := T.arithmetic.F) (nativeStagePlace T b)

/-- 1b. The actual rational monoid transport from Frobenioids I Prop. 2.2(ii),(iv),
applied to the stage-model presentation. -/
noncomputable def nativeStageRationalMonoidTransport :
    (nativeStageFrobenioidPresentation T b).preFrobenioid.RationalMonoidTransport :=
  Iut.FrobenioidRationalMonoidTransport.rationalMonoidTransport
    (nativeStageFrobenioidPresentation T b)

/-- 1c. Exact missing piece for the split Frobenioid: a characteristic
splitting of the stage-model rational monoid transport. -/
def NativeStageCharacteristicSplittingGap : Prop :=
  Nonempty ((nativeStageFrobenioidPresentation T b).preFrobenioid.CharacteristicSplitting
    (nativeStageRationalMonoidTransport T b))

/-- 1d. Conditional actual split Frobenioid presentation from a characteristic
splitting.  No characteristic splitting is constructed. -/
noncomputable def nativeStageSplitFrobenioidPresentation
    (C : (nativeStageFrobenioidPresentation T b).preFrobenioid.CharacteristicSplitting
      (nativeStageRationalMonoidTransport T b)) :
    Iut.SplitFrobenioidPresentation where
  frobenioid := nativeStageFrobenioidPresentation T b
  rationalMonoids := nativeStageRationalMonoidTransport T b
  splittingIndex := Unit
  splittingIndex_nonempty := ⟨()⟩
  splitting := fun _ => C

/-- 2. The actual O^triangle(A) object monoid at the stage-model carrier. -/
abbrev NativeStageOtriangleMonoid
    (A : (nativeStageFrobenioidPresentation T b).carrier) : Type :=
  (nativeStageFrobenioidPresentation T b).preFrobenioid.LinearBaseIdentityEndomorphism A

/-- 2. The actual O^times(A) units of O^triangle(A). -/
abbrev NativeStageOtimesUnits
    (A : (nativeStageFrobenioidPresentation T b).carrier) : Type :=
  Units (NativeStageOtriangleMonoid T b A)

/-- 2. Exact missing positivity/log-shell submonoid O_tri of O^times(A).
The repo has O^triangle and O^times but no O_tri positivity/log-shell
definition; this structure records the required data without an inhabitant. -/
structure NativeStageOtriSubmonoidSpec
    (A : (nativeStageFrobenioidPresentation T b).carrier) where
  Otri : Submonoid (NativeStageOtimesUnits T b A)
  positivityLogShellCondition : Prop
  qSection : Otri
  rootSection : Otri
  root_pow : rootSection ^ (2 * l.value) = qSection
  qSection_reflects_qVFamily : Prop

/-- 2. Exact missing O_tri submonoid datum. -/
def NativeStageOtriSubmonoidRequired
    (A : (nativeStageFrobenioidPresentation T b).carrier) : Prop :=
  Nonempty (NativeStageOtriSubmonoidSpec (l := l) (T := T) (b := b) A)

/-- 3. Exact missing q_v^(1/2l) O_tri section: it is the qSection/rootSection
pair of the spec together with the 2l-th-power equation.  No completion root
and no L are used. -/
def NativeStageQVFamilyOtriSectionRequired
    (A : (nativeStageFrobenioidPresentation T b).carrier) : Prop :=
  Nonempty (NativeStageOtriSubmonoidSpec (l := l) (T := T) (b := b) A)

end LeanFormal.IUT.XiFPaper.S369OtriSplitFrobenioidActual

end
