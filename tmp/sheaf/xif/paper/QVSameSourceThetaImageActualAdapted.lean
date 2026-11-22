import tmp.sheaf.xif.paper.LGPThetaActionActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual

/-!
# Same-source qVFamily theta image set and q-pilot scalar

The actual qVFamily q is the Clause-B parameter at each native bad place.  This
file constructs the same-source component-indexed theta image set

  qVThetaImageVector j
    : (b : Bad) -> (AlgebraicClosure (Completion (qVPlace T b)))^x
  qVThetaImageVector j b = lgpThetaValue T b j,

and the actual qVFamily q-pilot scalar

  qVThetaQPilotScalar = nativeQVPilotNormalizedLogMagnitude T.

The image vector is component-indexed over the actual bad places, not a
diagonal/constant tuple and not the fixed concrete theater thetaPacket.  No
comparison inequality is asserted.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.QVSameSourceThetaImageActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual component-indexed qVFamily theta image vector at signed label j. -/
noncomputable def qVThetaImageVector
    (j : SignedLabel l.value) :
    (b : Bad (nativePlaceSelection T)) →
      (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  fun b => lgpThetaValue T b j

/-- The component at b is the actual LGP theta value. -/
@[simp] theorem qVThetaImageVector_apply
    (j : SignedLabel l.value) (b : Bad (nativePlaceSelection T)) :
    qVThetaImageVector T j b = lgpThetaValue T b j := rfl

/-- The same-source qVFamily theta image set: all component-indexed vectors
over the actual bad places. -/
def qVThetaImageSet :
    Set ((b : Bad (nativePlaceSelection T)) →
      (AlgebraicClosure (Completion (qVPlace T b)))ˣ) :=
  Set.range (qVThetaImageVector T)

/-- The actual theta image set is nonempty. -/
theorem qVThetaImageSet_nonempty : (qVThetaImageSet T).Nonempty :=
  ⟨qVThetaImageVector T (zeroSignedLabel (l := l)), ⟨_, rfl⟩⟩

/-- The actual qVFamily q-pilot scalar: the normalized q_v magnitude. -/
noncomputable def qVThetaQPilotScalar : Real :=
  nativeQVPilotNormalizedLogMagnitude T

/-- The q-pilot scalar is the actual qVFamily normalized magnitude. -/
theorem qVThetaQPilotScalar_eq :
    qVThetaQPilotScalar T = nativeQVPilotNormalizedLogMagnitude T := rfl

/-- Same-source theta image set and q-pilot scalar data. -/
structure QVSameSourceThetaImageData where
  imageVector : SignedLabel l.value →
    (b : Bad (nativePlaceSelection T)) →
      (AlgebraicClosure (Completion (qVPlace T b)))ˣ
  imageVector_eq : imageVector = qVThetaImageVector T
  imageSet :
    Set ((b : Bad (nativePlaceSelection T)) →
      (AlgebraicClosure (Completion (qVPlace T b)))ˣ)
  imageSet_eq : imageSet = qVThetaImageSet T
  qPilotScalar : Real
  qPilotScalar_eq : qPilotScalar = qVThetaQPilotScalar T

/-- The actual same-source theta image/q-pilot scalar data. -/
noncomputable def qVSameSourceThetaImageData :
    QVSameSourceThetaImageData T where
  imageVector := qVThetaImageVector T
  imageVector_eq := rfl
  imageSet := qVThetaImageSet T
  imageSet_eq := rfl
  qPilotScalar := qVThetaQPilotScalar T
  qPilotScalar_eq := rfl

/-- The constructed q-pilot scalar is the qVFamily normalized magnitude. -/
@[simp] theorem qVSameSourceThetaImageData_qPilotScalar :
    (qVSameSourceThetaImageData T).qPilotScalar =
      nativeQVPilotNormalizedLogMagnitude T := rfl

end LeanFormal.IUT.XiFPaper.QVSameSourceThetaImageActualAdapted

end
