import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.ThetaPacketContractionProof
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # qVFamily / source theta-value bridge

The q-pilot q_v family is qVFamily T b, a FinitePlaceQCandidate in the
completion of the base Fmod place.  The source-theater theta value is

  I.thetaValueAt (n.val : Int) 0 j
    = (I.theaterAt (n.val : Int) 0).thetaPacket.scale j,

read from the actual source theater theta packet.

The paper theta value q_v^{j^2} would relate the two only after:

* identifying the source theater theta packet with the qVFamily q_v,
* taking the actual q_v norm / 2l-th root, and
* accounting for the mu_{2l} ambiguity of theta values.

No such identification is present in the source data.  This file constructs the
actual scalar bridge data and the exact relation proposition

  thetaValueAt n 0 j = ||(qVFamily T b).q||^(j^2),

proves the conditional equality from that proposition, and records the exact
source-theater-vs-qVFamily mismatch condition.  It does not fake the equality.
No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVThetaValueBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ThetaPacketContractionProof
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (n : ThetaPilotCarrier l)
variable (j : SignedLabel l.value)

/-- The actual qVFamily q norm at a native bad place. -/
noncomputable def qVFamilyQNorm : Real :=
  ‖(qVFamily T b).q‖

/-- The actual theta value read from the source theater packet. -/
noncomputable def sourceThetaValue : Real :=
  I.thetaValueAt (n.val : Int) 0 j

/-- The actual Gaussian exponent j^2. -/
def qvThetaExponent : Nat := (gaussExponent j.1).toNat

/-- The qVFamily power candidate (qVFamily norm)^(j^2). -/
noncomputable def qVFamilyThetaValue : Real :=
  (qVFamilyQNorm T b) ^ qvThetaExponent (l := l) j

/-- The source theta value is the source theater packet scale. -/
theorem sourceThetaValue_eq_scale :
    sourceThetaValue (I := I) n j =
      (I.theaterAt (n.val : Int) 0).thetaPacket.scale j := rfl

/-- Exact actual relation proposition between the source theta value and the
qVFamily norm power. -/
def QVThetaValueRelation : Prop :=
  sourceThetaValue (I := I) n j = qVFamilyThetaValue T b j

/-- Conditional bridge: the relation gives the equality. -/
theorem sourceThetaValue_eq_qVFamilyThetaValue_of_relation
    (h : QVThetaValueRelation (I := I) T b n j) :
    sourceThetaValue (I := I) n j = qVFamilyThetaValue T b j :=
  h

/-- Actual bridge data: the two scalars and the exact relation proposition. -/
structure QVThetaValueBridgeData where
  sourceTheta : Real
  sourceTheta_eq : sourceTheta = sourceThetaValue (I := I) n j
  qvNorm : Real
  qvNorm_eq : qvNorm = qVFamilyQNorm T b
  qvTheta : Real
  qvTheta_eq : qvTheta = qVFamilyThetaValue T b j
  relation : Prop
  relation_eq : relation = (sourceTheta = qvTheta)

/-- The actual bridge data from qVFamily and thetaValueAt. -/
noncomputable def qvThetaValueBridgeData :
    QVThetaValueBridgeData (I := I) T b n j where
  sourceTheta := sourceThetaValue (I := I) n j
  sourceTheta_eq := rfl
  qvNorm := qVFamilyQNorm T b
  qvNorm_eq := rfl
  qvTheta := qVFamilyThetaValue T b j
  qvTheta_eq := rfl
  relation := sourceThetaValue (I := I) n j = qVFamilyThetaValue T b j
  relation_eq := rfl

/-- Exact mismatch condition: the source-theater theta packet q differs from
the qVFamily q norm. -/
def SourceTheaterQNeQVFamily : Prop :=
  (sourceTheater l).thetaPacket.q ≠ qVFamilyQNorm T b

/-- Exact mismatch at the relation level. -/
def QVThetaValueMismatch : Prop :=
  ¬ QVThetaValueRelation (I := I) T b n j

/-- The relation is equivalent to equality of the bridge scalars. -/
theorem qvThetaValueRelation_iff_bridgeData :
    QVThetaValueRelation (I := I) T b n j ↔
      (qvThetaValueBridgeData (I := I) T b n j).sourceTheta =
        (qvThetaValueBridgeData (I := I) T b n j).qvTheta :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.QVThetaValueBridgeActual

end
