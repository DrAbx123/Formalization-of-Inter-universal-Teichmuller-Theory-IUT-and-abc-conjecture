import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.C3GaussianThetaPacketActual
import tmp.sheaf.xif.paper.S3133S3131NormalizedReadoutAdapterActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.n8.closure.C3Actual

/-!
# Gaussian model components for mainline M0/M2/M3 (component, not paper object)

COMPONENT, not a paper object.  Named consumers: mainline task-20 model map
M0/M2/M3 (S3131Stage2ModelMapActual fields) and lattice
S3137NativeToC3SameCReadoutActual (R1).

Source: IUT I, Definition 3.1 (initial Theta data); IUT I, Example 3.2, (iv)
(q_v parameters); IUT II, Remark 2.5.1, (i) (theta values); IUT III,
Definition 3.8, (i), p. 112-113; Remark 3.1.1, (ii)-(iv), p. 95-97.

Actual Gaussian model available in the tree (no fake inputs):
* S1280Arithmetic = concreteGaussianInitialThetaArithmeticData (actual Q(i),
  actual base-changed split multiplicative curve), with the actual bad place
  above 5 and the assembled Definition 3.1 prefix conditional on the D5-D9
  paper clauses (S1280SourceData_of_remaining);
* the actual Gaussian q-parameter value at the bad place,
  (1/5)^order, computed in S1280ReductionClause_qParameter_eq;
* the actual Stage-2 image actualGaussianC3 (c3WithSourceTheaterTheta) whose
  theta packet is the actual Gaussian packet with q = 1/5.

Proved here: M0 source-arithmetic match for the canonical T from an actual
SourceCompletion with the model arithmetic; M0 Stage-2 arithmetic match for the
assembled S1280 Definition 3.1 data; the actual Gaussian q-parameter computation;
the actual Stage-2 theta packet value q = 1/5.  The remaining M0-M3
identifications are recorded as field-level exact Missing with page references,
not inhabited.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-! ## M0: arithmetic/source model match -/

/-- Exact source-arithmetic model match for a native initial Theta datum: its
arithmetic is the concrete Gaussian initial Theta data. -/
def S3133GaussianModelArithmeticMatch
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  T.arithmetic = concreteGaussianInitialThetaArithmeticData l

/-- Exact Stage-2 (Definition 3.1 data) arithmetic model match. -/
def S3133GaussianStage2ArithmeticMatch
    (S : SourceDefinition31Data.{0} l) : Prop :=
  S.arithmetic = concreteGaussianInitialThetaArithmeticData l

/-- The S1280 actual arithmetic input is the concrete Gaussian arithmetic. -/
theorem S1280Arithmetic_eq_concreteGaussian (l : PrimeGeFive) :
    S1280Arithmetic l = concreteGaussianInitialThetaArithmeticData l := rfl

/-- M0, native side: a SourceCompletion whose arithmetic is the model
arithmetic packages a native datum satisfying the model match (proved). -/
theorem S3133GaussianModelArithmeticMatch_of_completion
    (C : SourceCompletion.{0} l)
    (h : C.arithmetic = concreteGaussianInitialThetaArithmeticData l) :
    S3133GaussianModelArithmeticMatch C.toSourceNativeInitialThetaData := by
  unfold S3133GaussianModelArithmeticMatch
  rw [C.toSourceNative_arithmetic, h]

/-- M0, Stage-2 side: the assembled S1280 Definition 3.1 data (conditional on
the D5-D9 paper clauses) satisfies the model arithmetic match (proved). -/
theorem S3133GaussianStage2ArithmeticMatch_of_S1280
    (l : PrimeGeFive) (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    S3133GaussianStage2ArithmeticMatch
      (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) := by
  unfold S3133GaussianStage2ArithmeticMatch
  rw [S1280SourceData_of_remaining_arithmetic]

/-- M0 bridge (proved): if the native T and the Stage-2 data S both carry the
model arithmetic, then they carry the SAME arithmetic input. -/
theorem S3133GaussianArithmeticMatch_bridge
    (T : SourceNativeInitialThetaData.{0} l) (S : SourceDefinition31Data.{0} l)
    (hT : S3133GaussianModelArithmeticMatch T)
    (hS : S3133GaussianStage2ArithmeticMatch S) :
    T.arithmetic = S.arithmetic := hT.trans hS.symm

/-! ## M2: actual Gaussian q-parameter value -/

/-- Exact Gaussian q-parameter value at the actual bad place: the model-side
q-parameter is (1/5)^order (actual computation, not a normalized constant). -/
theorem S3133GaussianModelQParameter_value
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).qParameter b =
      ((5 : Real)⁻¹) ^ (badPlaceQCandidate (S1280Selection l) b).order :=
  S1280ReductionClause_qParameter_eq l b

/-- Exact M2 q-parameter match Prop: every actual Gaussian q_v candidate has
completion norm 1/5 (IUT I Example 3.2(iv); IUT III Definition 3.8(i)). -/
def S3133GaussianQParameterMatch
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  ∀ b : Bad (nativePlaceSelection T), ‖(qVFamily T b).q‖ = ((5 : Real)⁻¹)

/-! ## M3: actual Gaussian theta-packet value (Stage-2 side) -/

/-- The actual Gaussian theta packet has q = 1/5. -/
theorem S3133GaussianThetaPacket_q :
    (actualGaussianThetaPacket (l := l)).q = ((5 : Real)⁻¹) :=
  actualGaussianThetaPacket_q_eq_inv_five (l := l)

/-- The actual Stage-2 image (c3WithSourceTheaterTheta) carries exactly the
actual Gaussian theta packet. -/
theorem S3133GaussianStage2ThetaPacket_eq
    (D : SourcePilotRegionDonors I) :
    (actualGaussianC3 (l := l) (V := V) (I := I) D).thetaPacket =
      actualGaussianThetaPacket (l := l) :=
  actualGaussianC3_thetaPacket (l := l) (V := V) (I := I) D

/-- The actual Stage-2 image theta packet has q = 1/5. -/
theorem S3133GaussianStage2ThetaPacket_q
    (D : SourcePilotRegionDonors I) :
    (actualGaussianC3 (l := l) (V := V) (I := I) D).thetaPacket.q =
      ((5 : Real)⁻¹) :=
  actualGaussianC3_thetaPacket_q_eq_inv_five (l := l) (V := V) (I := I) D

/-- Exact M3 theta-value match Prop: the actual source-theater theta values and
the Stage-2 C3 theta values agree at every label (IUT II Remark 2.5.1(i)). -/
def S3133GaussianThetaValueMatch
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  ∀ j : SignedLabel l.value,
    (sourceTheater l).thetaPacket.scale j = C3.thetaPacket.scale j

/-- M3 PROVED for the actual Gaussian Stage-2 image: its theta packet is the
actual source-theater Gaussian packet, so the theta values agree (given the
actual C3 donors D). -/
theorem S3133GaussianThetaValueMatch_actualGaussian
    (D : SourcePilotRegionDonors I) :
    S3133GaussianThetaValueMatch (l := l) (V := V) (I := I)
      (actualGaussianC3 (l := l) (V := V) (I := I) D) := by
  intro j
  rw [← actualGaussianThetaPacket_eq_sourceTheater (l := l)]
  rw [actualGaussianC3_thetaPacket (l := l) (V := V) (I := I) D]

/-! ## Final M-list residual (field-level exact Missing) -/

/-- Field-level exact Missing for the Gaussian model map (mainline M0/M2/M3).
The actual pieces are proved above; the residual fields are not inhabited. -/
structure S3133GaussianModelMapResidual : Type where
  /-- exact Missing: an actual SourceCompletion above the Gaussian model
  arithmetic (D4 boundary; S1280's first missing field is the torsion clause) -/
  sourceCompletionSupply : Prop
  /-- exact source-arithmetic match for the native T (Prop; proved form above
  from a supplied SourceCompletion) -/
  arithmeticModelMatch : Prop
  /-- exact M2 q-parameter match native q_v vs the Gaussian q = 1/5 model -/
  qParameterMatch : Prop
  /-- exact M3 theta-value match native theta values vs the Stage-2 C3 packet -/
  thetaValueMatch : Prop

/-- The existence of the missing Gaussian model-map residual. -/
def S3133GaussianModelMapResidualData : Prop :=
  Nonempty S3133GaussianModelMapResidual

end LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
