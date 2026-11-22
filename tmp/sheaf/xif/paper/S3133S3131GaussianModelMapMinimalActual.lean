import tmp.sheaf.xif.paper.S3133S3131GaussianModelComponentsActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.S3130QCSourceActual
import tmp.sheaf.xif.paper.S3133S3131PlaceIndexComparisonActual
import tmp.sheaf.xif.paper.S3133BadToAllPlaceIndexInjectionActual
import tmp.sheaf.n8.closure.C3Actual

/-!
# Minimal Gaussian model-map residual and R1 interface (component, not paper object)

COMPONENT, not a paper object.  Named consumers: lattice S3137 R1
(NativeToC3SameCReadoutIdentification), mainline task-20 M-list.

Source: IUT I, Definition 3.1 (initial Theta data, solver data); IUT I,
Example 3.2, (iv) (q_v parameters); IUT II, Remark 2.5.1, (i) (theta values);
IUT III, Definition 3.8, (i), p. 112-113; Remark 3.1.1, (ii)-(iv), p. 95-97.

M2 attack result.  The Batch-A source q is the clause-B comparison parameter at
the actual lifted F-place (PROVED, definitional):

  qVFamily T b = (choice (T.clauseB.q_comparison (lift b) _)).parameter,
  (s3130QCSourceData T b h).qV = qVFamily T b.

The Gaussian model q lives at the BASE Fmod place.  The needed base-q descent
(F-completion -> Fmod completion) and its value |q| = 1/5 are NOT available from
the actual inputs (see ActualC3DonorFromNative.MissingBaseQData /
MissingC3DonorData for the exact source missing data; that file is not imported
here because it is not compiled).  M2 is therefore SHRUNK to the exact
conditional Prop S3133GaussianQParameterMatchAtBase: at bad places above 5 the
clause-B q has norm 1/5.  Given the M1 index comparison placing all bad places
above 5, this implies the earlier S3133GaussianQParameterMatch.

This file assembles the minimal Gaussian model-map residual using the PROVED M0
and M3 parts (S3133S3131GaussianModelComponentsActual) and exposes the R1
interface for lattice.  Only genuine missing fields remain: M1 (bad <-> all-place
index injection, genuine source placeToMod missing) and shrunk M2 (base q data +
Gaussian value).  No proof of a residual field is assumed.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3130QCSourceActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3133BadToAllPlaceIndexInjectionActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-! ## M2 attack: the clause-B q is the actual source q (PROVED) -/

/-- The actual qVFamily at a bad place is the clause-B comparison parameter at
the actual lifted F-place (definitional). -/
theorem S3133M2_clauseB_q_parameter
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    qVFamily T b =
      (Classical.choice
        (T.clauseB.q_comparison ((nativeBadLift T).lift b)
          (by
            rw [(nativeBadLift T).lift_comap b]
            exact b.2))).parameter :=
  qVFamily_eq_comparisonParameter T b

/-- The Batch-A Q_C source q is the same clause-B parameter (PROVED). -/
theorem S3133M2_QCSource_qV_eq_clauseB
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    (s3130QCSourceData T b h).qV =
      (Classical.choice
        (T.clauseB.q_comparison ((nativeBadLift T).lift b)
          (by
            rw [(nativeBadLift T).lift_comap b]
            exact b.2))).parameter := by
  rw [s3130QCSourceData_qV, S3133M2_clauseB_q_parameter]

/-! ## M2 shrunk exact missing: Gaussian value at bad places above 5 -/

/-- SHRUNK exact M2 residual: at bad places whose rational prime is 5, the
clause-B q has completion norm 1/5.  This is the Gaussian model value
(IUT I Example 3.2(iv); IUT III Definition 3.8(i)); the base-q descent is the
genuine source missing datum. -/
def S3133GaussianQParameterMatchAtBase
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    (completionRationalPrime (nativeBadToFPlace T b)).val = 5 →
      ‖(qVFamily T b).q‖ = ((5 : Real)⁻¹)

/-- If all bad places lie above 5 (the M1 index comparison content), the shrunk
M2 residual implies the full Gaussian q-parameter match. -/
theorem S3133GaussianQParameterMatch_of_atBase
    (T : SourceNativeInitialThetaData.{0} l)
    (h5 : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime (nativeBadToFPlace T b)).val = 5)
    (h : S3133GaussianQParameterMatchAtBase T) :
    S3133GaussianQParameterMatch T :=
  fun b => h b (h5 b)

/-! ## Minimal residual assembly (only genuine missing fields) -/

/-- Minimal Gaussian model-map residual: an actual SourceCompletion above the
model arithmetic (M0 supply, paper D4 input), the M1 bad<->all-place index
injection proposition, and the shrunk M2 base-q/Gaussian-value proposition.
M0 and M3 are PROVED from these data in the component theorems below. -/
structure S3133GaussianModelMapResidualMinimal
    (D : SourcePilotRegionDonors I) where
  /-- actual SourceCompletion above the Gaussian model arithmetic (M0 supply) -/
  C : SourceCompletion.{0} l
  arithmetic_eq : C.arithmetic = concreteGaussianInitialThetaArithmeticData l
  /-- M1 exact residual: bad <-> all-place index injection (shape in
  S3133BadToAllPlaceIndexInjectionData; genuine source placeToMod missing) -/
  m1_indexInjection : Prop
  /-- M2 shrunk exact residual: base-q data + Gaussian norm at bad places above 5 -/
  m2_baseQMatch : Prop
  m2_baseQMatch_eq :
    m2_baseQMatch = S3133GaussianQParameterMatchAtBase C.toSourceNativeInitialThetaData

/-- The M0 part of the minimal residual is PROVED from the supplied actual
SourceCompletion with the model arithmetic. -/
theorem S3133GaussianModelMapResidualMinimal_m0
    (D : SourcePilotRegionDonors I)
    (R : S3133GaussianModelMapResidualMinimal D) :
    S3133GaussianModelArithmeticMatch R.C.toSourceNativeInitialThetaData :=
  S3133GaussianModelArithmeticMatch_of_completion R.C R.arithmetic_eq

/-- The M3 part of the minimal residual is PROVED for the actual Gaussian
Stage-2 image from the actual donors D. -/
theorem S3133GaussianModelMapResidualMinimal_m3
    (D : SourcePilotRegionDonors I) :
    S3133GaussianThetaValueMatch (l := l) (V := V) (I := I)
      (actualGaussianC3 (l := l) (V := V) (I := I) D) :=
  S3133GaussianThetaValueMatch_actualGaussian (l := l) (V := V) (I := I) D

/-- Remaining residual of the minimal model map: exactly M1 and shrunk M2. -/
def S3133GaussianModelMapRemaining
    (D : SourcePilotRegionDonors I)
    (R : S3133GaussianModelMapResidualMinimal D) : Prop :=
  R.m1_indexInjection ∧ R.m2_baseQMatch

/-! ## R1 interface for lattice (read-only consumer) -/

/-- The exposed R1 interface: PROVED M0 (from the supplied SourceCompletion with
model arithmetic) and PROVED M3 (actual Gaussian Stage-2 image from donors), with
the remaining residual exactly M1 + shrunk M2. -/
theorem S3137R1_interface
    (D : SourcePilotRegionDonors I)
    (R : S3133GaussianModelMapResidualMinimal D) :
    S3133GaussianModelArithmeticMatch R.C.toSourceNativeInitialThetaData ∧
      S3133GaussianThetaValueMatch (l := l) (V := V) (I := I)
        (actualGaussianC3 (l := l) (V := V) (I := I) D) ∧
      (R.m1_indexInjection ∧ R.m2_baseQMatch ↔
        S3133GaussianModelMapRemaining D R) :=
  ⟨S3133GaussianModelMapResidualMinimal_m0 D R,
    S3133GaussianModelMapResidualMinimal_m3 D,
    Iff.rfl⟩

end LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual
