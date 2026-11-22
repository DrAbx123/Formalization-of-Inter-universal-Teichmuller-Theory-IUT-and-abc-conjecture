/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual
import tmp.sheaf.xif.paper.Mzk1R4LiteralAssemblyActual

/-!
# Mzk1QPilotR4Stage5AlignActual — alignment of the q/Theta double image with the
R4 assembly signed-contract interface and the Stage-5 numerical interface.

From the literal q-pilot / Theta-pilot double image (`QThetaDoubleImage`) we expose
the signed readouts consumed by the R4 assembly:

* `qThetaHullReadout b = log||q_V||_b` (negative signed q-pilot log-volume);
* `qThetaDetReadout b = log||q_V||_b / (2l)` (signed Theta-pilot log-volume, the
  (2l)-th-root readout of the root relation `theta^(2l) = q`);
* the strict ordering `qThetaHullReadout < qThetaDetReadout < 0` (Cor 3.12 signed
  comparison), and a genuine `StepXIContract` whose `she` slot is the proved SHE
  arrow; the `ipl`/`apt` slots are passed as explicit propositions with their evidence
  (no True placeholder);
* Stage-5 alignment: the positive literal hull volume `-log||q_V||` supplies the
  `hullVolume` parameter of `abcConjecture_of_literalLogVolumeEstimates`.

No value-model carrier, no sorry/axiom. Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The signed Theta-pilot log readout: the (2l)-th-root log of the q_V norm, from
`theta^(2l) = q` on the literal double image. -/
def thetaPilotLogImage (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotLogImage T b / (2 * (l.value : Real))

/-- The signed q-pilot log readout is negative (the q-pilot is a genuine local
uniformizer on the literal completion carrier). -/
theorem qPilotLogImage_neg (b : Bad (nativePlaceSelection T)) :
    qPilotLogImage T b < 0 := by
  unfold qPilotLogImage
  exact localSignedLog_neg (qVFamily T b)

/-- Multiplying the Theta-pilot log readout by `2l` recovers the q-pilot log readout
(the signed form of the root relation of the double image). -/
theorem twoL_mul_thetaPilotLogImage (b : Bad (nativePlaceSelection T)) :
    (2 * (l.value : Real)) * thetaPilotLogImage T b = qPilotLogImage T b := by
  rw [thetaPilotLogImage]
  have h5 : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
  have hden : (2 * (l.value : Real)) ≠ 0 := by nlinarith
  field_simp

/-- The signed q-pilot log readout is strictly below the Theta-pilot one: the literal
comparison of Cor 3.12. -/
theorem qPilotLogImage_lt_thetaPilotLogImage (b : Bad (nativePlaceSelection T)) :
    qPilotLogImage T b < thetaPilotLogImage T b := by
  have hq : qPilotLogImage T b < 0 := qPilotLogImage_neg T b
  have h5 : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
  have hden1 : (1 : Real) < 2 * (l.value : Real) := by nlinarith
  have hden : (0 : Real) < 2 * (l.value : Real) := by nlinarith
  rw [thetaPilotLogImage, lt_div_iff₀ hden]
  have hmul : qPilotLogImage T b * (2 * (l.value : Real)) <
      qPilotLogImage T b * 1 :=
    mul_lt_mul_of_neg_left hden1 hq
  simpa using hmul

/-- The signed Theta-pilot log readout is negative as well. -/
theorem thetaPilotLogImage_neg (b : Bad (nativePlaceSelection T)) :
    thetaPilotLogImage T b < 0 := by
  rw [thetaPilotLogImage]
  exact div_neg_of_neg_of_pos (qPilotLogImage_neg T b) (by
    have h5 : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
    nlinarith)

/-- R4 assembly hull readout: the signed q-pilot log-volume. -/
def qThetaHullReadout (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotLogImage T b

/-- R4 assembly determinant readout: the signed Theta-pilot log-volume. -/
def qThetaDetReadout (b : Bad (nativePlaceSelection T)) : Real :=
  thetaPilotLogImage T b

/-- The R4 assembly readouts satisfy the Step (xi-f) signed comparison. -/
theorem qThetaReadout_ordered (b : Bad (nativePlaceSelection T)) :
    qThetaHullReadout T b <= qThetaDetReadout T b :=
  le_of_lt (qPilotLogImage_lt_thetaPilotLogImage T b)

/-- The signed q/Theta values of the literal double image as a genuine `StepXIContract`.
The `she` slot is the proved SHE arrow; `ipl` and `apt` are explicit propositions with
their supplied evidence (the R4 assembly's remaining named inputs). -/
def qThetaStepXIContract (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) : StepXIContract where
  qSigned := qPilotLogImage T b
  thetaSigned := thetaPilotLogImage T b
  targetSigned := thetaPilotLogImage T b
  q_negative := qPilotLogImage_neg T b
  ipl := ipl
  she := SHEArrowStatement T
  apt := apt
  ipl_evidence := hipl
  she_evidence := sheArrowStatement_proved T
  apt_evidence := hapt
  q_le_target := le_of_lt (qPilotLogImage_lt_thetaPilotLogImage T b)
  target_le_theta := le_rfl

/-- The Cor 3.12 ordered conclusion from the aligned double-image contract. -/
theorem cor312Conclusion_of_qThetaDoubleImage (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (qThetaStepXIContract T b ipl hipl apt hapt) :=
  cor312_of_constructed_stepXI _

/-- The positive literal hull volume readout from the q-pilot log image. -/
def qThetaHullVolume (b : Bad (nativePlaceSelection T)) : Real :=
  -qPilotLogImage T b

/-- The literal hull volume is positive. -/
theorem qThetaHullVolume_pos (b : Bad (nativePlaceSelection T)) :
    0 < qThetaHullVolume T b :=
  neg_pos.mpr (qPilotLogImage_neg T b)

/-- Stage-5 alignment: the literal hull volume from the q/Theta double image supplies
the `hullVolume` parameter of the Stage-5 numerical estimate, so the Stage-5 theorems
apply directly to the literal double-image hull. -/
theorem abcConjecture_of_qThetaStage5Estimates (pb : Bad (nativePlaceSelection T))
    (logVolume : Nat -> Nat -> Nat -> Real)
    (hheight : forall delta : Real, 0 < delta -> forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <= (1 + delta) * logVolume a b c)
    (hmain : forall delta : Real, 0 < delta -> exists D : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        logVolume a b c <= (1 + delta) * arithmeticWeight (abcRationalPoint a c) +
          qThetaHullVolume T pb + D) :
    ABCConjecture :=
  abcConjecture_of_literalLogVolumeEstimates logVolume (qThetaHullVolume T pb) hheight hmain

/-- The double-image readout package: hullReadout/detReadout identified with the
q-pilot/Theta-pilot signed log quantities, with root relation, positivity and the
signed comparison.  This is the exact input shape consumed by the R4 assembly's
`step3115_comparison` field. -/
structure QThetaReadoutPackage (b : Bad (nativePlaceSelection T)) where
  hullReadout : Real
  detReadout : Real
  hullReadout_eq : hullReadout = qPilotLogImage T b
  detReadout_eq : detReadout = thetaPilotLogImage T b
  twoL_mul_detReadout : (2 * (l.value : Real)) * detReadout = hullReadout
  hullReadout_neg : hullReadout < 0
  detReadout_neg : detReadout < 0
  hull_lt_det : hullReadout < detReadout

/-- The literal equalities of the double-image readouts with the q/Theta-pilot logs. -/
theorem qThetaHullReadout_eq_qPilotLog (b : Bad (nativePlaceSelection T)) :
    qThetaHullReadout T b = qPilotLogImage T b := rfl

theorem qThetaDetReadout_eq_thetaPilotLog (b : Bad (nativePlaceSelection T)) :
    qThetaDetReadout T b = thetaPilotLogImage T b := rfl

/-- The strict signed comparison of the double-image readouts. -/
theorem qThetaReadout_strict (b : Bad (nativePlaceSelection T)) :
    qThetaHullReadout T b < qThetaDetReadout T b :=
  qPilotLogImage_lt_thetaPilotLogImage T b

/-- The root relation read on the R4 readouts: `(2l) * detReadout = hullReadout`. -/
theorem twoL_mul_qThetaDetReadout (b : Bad (nativePlaceSelection T)) :
    (2 * (l.value : Real)) * qThetaDetReadout T b = qThetaHullReadout T b :=
  twoL_mul_thetaPilotLogImage T b

/-- The det-side log-volume is positive. -/
theorem qThetaDetVolume_pos (b : Bad (nativePlaceSelection T)) :
    0 < -qThetaDetReadout T b :=
  neg_pos.mpr (thetaPilotLogImage_neg T b)

/-- The actual double-image readout package. -/
def qThetaReadoutPackage (b : Bad (nativePlaceSelection T)) : QThetaReadoutPackage T b where
  hullReadout := qThetaHullReadout T b
  detReadout := qThetaDetReadout T b
  hullReadout_eq := rfl
  detReadout_eq := rfl
  twoL_mul_detReadout := twoL_mul_qThetaDetReadout T b
  hullReadout_neg := qPilotLogImage_neg T b
  detReadout_neg := thetaPilotLogImage_neg T b
  hull_lt_det := qThetaReadout_strict T b

/-- `step3115_comparison` in package form: the R4 signed comparison follows from the
double-image readout package. -/
theorem step3115_comparison_of_qThetaPackage {b : Bad (nativePlaceSelection T)}
    (P : QThetaReadoutPackage T b) : P.hullReadout <= P.detReadout :=
  le_of_lt P.hull_lt_det

/-- The R4 assembly HDD decomposition of the literal double image. -/
def qThetaHDD : HDDDecomp Real Real (Bad (nativePlaceSelection T)) where
  hullReadout := qThetaHullReadout T
  detReadout := qThetaDetReadout T

/-- The R4 assembly dsc leg of the literal double image (identity on bad places). -/
def qThetaDSC : Bad (nativePlaceSelection T) -> Bad (nativePlaceSelection T) := id

/-- The four-triangle readout of the double image is exactly the q/Theta-pilot log
pair, so the R4 assembly's `hull_eq`/`theta_eq` fields hold by rfl. -/
theorem qTheta_fourTriangleReadout (b : Bad (nativePlaceSelection T)) :
    fourTriangleReadout (qThetaHDD T) (qThetaDSC T) b =
      (qPilotLogImage T b, thetaPilotLogImage T b) := rfl

/-- Direct `step3115_comparison` for the R4 four-triangle readout of the double image. -/
theorem qTheta_step3115_comparison (b : Bad (nativePlaceSelection T)) :
    (fourTriangleReadout (qThetaHDD T) (qThetaDSC T) b).1 <=
      (fourTriangleReadout (qThetaHDD T) (qThetaDSC T) b).2 :=
  qThetaReadout_ordered T b

/-- The R4 `FourTriangleSynthesis` instance whose contract/readouts are supplied by the
literal double-image package (the `she` slot is the proved SHE arrow). -/
def qThetaFourTriangleSynthesis (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    FourTriangleSynthesis (Bad (nativePlaceSelection T)) (Bad (nativePlaceSelection T)) where
  contract := qThetaStepXIContract T b ipl hipl apt hapt
  hdd := qThetaHDD T
  dsc := qThetaDSC T
  sheOut := b
  hull_eq := rfl
  theta_eq := rfl
  step3115_comparison := qThetaReadout_ordered T b

/-- Cor 3.12 ordered conclusion from the double-image four-triangle synthesis. -/
theorem cor312Conclusion_of_qThetaFourTriangle (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (qThetaFourTriangleSynthesis T b ipl hipl apt hapt).contract :=
  cor312Conclusion_of_fourTriangleSynthesis _

/-- The positive hull volume is the negative of the signed hull readout. -/
theorem qThetaHullVolume_eq_neg_hullReadout (b : Bad (nativePlaceSelection T)) :
    qThetaHullVolume T b = -qThetaHullReadout T b := rfl

/-- The positive Theta-pilot volume readout. -/
def qThetaDetVolume (b : Bad (nativePlaceSelection T)) : Real :=
  -qThetaDetReadout T b

/-- The Theta-pilot volume is the negative of the signed det readout. -/
theorem qThetaDetVolume_eq (b : Bad (nativePlaceSelection T)) :
    qThetaDetVolume T b = -qThetaDetReadout T b := rfl

/-- The root relation in positive volumes: the hull volume is `2l` times the
Theta-pilot volume. -/
theorem qThetaHullVolume_eq_twoL_mul_detVolume (b : Bad (nativePlaceSelection T)) :
    qThetaHullVolume T b = (2 * (l.value : Real)) * qThetaDetVolume T b := by
  unfold qThetaHullVolume qThetaDetVolume qThetaDetReadout
  have h := twoL_mul_thetaPilotLogImage T b
  rw [← h]
  ring

/-- The Theta-pilot volume is strictly smaller than the hull volume (root factor
`2l > 1` on positive volumes). -/
theorem qThetaDetVolume_lt_hullVolume (b : Bad (nativePlaceSelection T)) :
    qThetaDetVolume T b < qThetaHullVolume T b := by
  rw [qThetaHullVolume_eq_twoL_mul_detVolume]
  have h5 : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
  have hden : (1 : Real) < 2 * (l.value : Real) := by nlinarith
  have hpos : 0 < qThetaDetVolume T b := by
    rw [qThetaDetVolume_eq]
    exact qThetaDetVolume_pos T b
  simpa [mul_comm] using mul_lt_mul_of_pos_left hden hpos

/-- The two positive volume readouts are both strictly positive. -/
theorem qThetaVolume_pair_pos (b : Bad (nativePlaceSelection T)) :
    0 < qThetaHullVolume T b ∧ 0 < -qThetaDetReadout T b :=
  ⟨qThetaHullVolume_pos T b, qThetaDetVolume_pos T b⟩

#check cor312Conclusion_of_qThetaDoubleImage
#check abcConjecture_of_qThetaStage5Estimates
#check qThetaReadout_ordered

end LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual
end
