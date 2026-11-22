import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # Theta packet/image data from the same qVFamily as the q-pilot scalar

The q-pilot scalar is built from the actual clause-B qVFamily.  Theta image data
must be built from the SAME qVFamily; no equality with a different source
theater q (e.g. the Gaussian q = 1/5 packet) is needed or asserted.

For each native bad place b:

  qVFamilyQNorm b = ||(qVFamily T b).q||,
  qVFamilyThetaPacket b = FiniteThetaPacket.ofQ (qVFamilyQNorm b) (positive),

so qVFamilyThetaPacket b is the actual finite theta packet with
q = qVFamilyQNorm b and scales realThetaValue (qVFamilyQNorm b) j.  The theta
image set is the finite range of these actual theta values.  The q-pilot signed
scalar and the theta image data therefore share the same qVFamily source.

No cross-theater equality and no value-layer function space is used.  No fake
inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamThetaImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily q norm at a bad place. -/
noncomputable def qVFamilyQNorm : Real :=
  ‖(qVFamily T b).q‖

/-- The qVFamily q norm is positive. -/
theorem qVFamilyQNorm_pos : 0 < qVFamilyQNorm T b :=
  norm_pos_iff.mpr (qVFamily T b).q_ne_zero

/-- The actual finite theta packet of the same qVFamily q. -/
noncomputable def qVFamilyThetaPacket : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ (qVFamilyQNorm T b) (qVFamilyQNorm_pos T b)

/-- The packet q is exactly the qVFamily norm. -/
theorem qVFamilyThetaPacket_q :
    (qVFamilyThetaPacket T b).q = qVFamilyQNorm T b := rfl

/-- The actual theta value at a label, read from the same qVFamily packet. -/
noncomputable def qVFamilyThetaValue
    (j : SignedLabel l.value) : Real :=
  (qVFamilyThetaPacket T b).scale j

/-- The actual theta log formula from the same qVFamily. -/
theorem qVFamilyThetaValue_log
    (j : SignedLabel l.value) :
    Real.log (qVFamilyThetaValue T b j) =
      (gaussExponent j.1).toNat * Real.log (qVFamilyQNorm T b) :=
  (qVFamilyThetaPacket T b).log_scale j

/-- Actual theta image set from the same qVFamily: the finite set of its theta
values. -/
def qVFamilyThetaImageSet : Set Real :=
  Set.range (qVFamilyThetaValue T b)

/-- The theta image set is finite. -/
theorem qVFamilyThetaImageSet_finite : (qVFamilyThetaImageSet T b).Finite :=
  Set.finite_range _

/-- The actual q-pilot signed log scalar from the same qVFamily. -/
noncomputable def qVFamilySignedLog : Real :=
  localSignedLog (qVFamily T b)

/-- The q-pilot signed scalar is the negative qVFamily magnitude. -/
theorem qVFamilySignedLog_eq_neg_magnitude :
    qVFamilySignedLog T b = -localLogMagnitude (qVFamily T b) :=
  localSignedLog_eq_neg_magnitude (qVFamily T b)

/-- Actual same-source data: qVFamily scalar, theta packet, theta values and
image set. -/
structure QVFamThetaImageData where
  qNorm : Real
  qNorm_eq : qNorm = qVFamilyQNorm T b
  signedLog : Real
  signedLog_eq : signedLog = qVFamilySignedLog T b
  packet : FiniteThetaPacket l
  packet_eq : packet = qVFamilyThetaPacket T b
  thetaValue : SignedLabel l.value → Real
  thetaValue_eq : thetaValue = qVFamilyThetaValue T b
  imageSet : Set Real
  imageSet_eq : imageSet = qVFamilyThetaImageSet T b

/-- The actual same-source data constructor. -/
noncomputable def qvFamThetaImageData :
    QVFamThetaImageData T b where
  qNorm := qVFamilyQNorm T b
  qNorm_eq := rfl
  signedLog := qVFamilySignedLog T b
  signedLog_eq := rfl
  packet := qVFamilyThetaPacket T b
  packet_eq := rfl
  thetaValue := qVFamilyThetaValue T b
  thetaValue_eq := rfl
  imageSet := qVFamilyThetaImageSet T b
  imageSet_eq := rfl

/-- Both the q-pilot scalar and the theta packet use the same qVFamily q. -/
theorem qvFamThetaImageData_same_q :
    (qvFamThetaImageData T b).packet.q =
      (qvFamThetaImageData T b).qNorm := rfl

end LeanFormal.IUT.XiFPaper.QVFamThetaImageActual

end
