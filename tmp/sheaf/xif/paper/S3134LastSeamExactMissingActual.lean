import tmp.sheaf.xif.paper.S3134FourthTriangleCompositionStatusActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.QPilotObjectActual

/-!
# S3134 task-35: shrinking the last-seam identification to field-level actual data

**Component, not paper object.**  The last seam of the fourth triangle is the
identification of the actual fourth-triangle signed readouts with the Stage-2
`(C3, P)` readouts:

  `S3134FourthTriangleToC3ReadoutIdentification D C3 P`
    = (signed Theta readout of the actual hull+det after SHE = `thetaPilotHullLogVolumeReal C3`
       AND signed q readout of the actual `(1,0)` q-parameter = `qPilotLogVolumeReading P`)

This file does not construct that identification (no D <-> C3 carrier
identification exists: D's readout is the HDD det log-volume of the transported
`LocalFieldProductHull` hull of D's conditional factors, while the C3 readout is
the tensor Haar log-volume of `actualHolomorphicHull C3 actualUnitRegion`;
hull's task-30 file records that as the minimal exact missing).  Instead it
shrinks the named identification to a *field-level* exact missing with each
side written in its actual unfolded form, and reduces each half to the equality
of concrete actual numbers:

* q half: `|log (S3134QParameter J)| = |log ‖P.line.C3.q.q‖|`, i.e. the
  equality of the actual fourth-triangle q magnitude with the actual C3 source
  completion q magnitude of the same fixed input C (IUT I Def. 3.1(b) q
  parameters; IUT III Def. 3.8(i) p. 112, Prop. 3.9(i) p. 115);
* Theta half: `-(D.detData.logVolume (S3134ThetaHullRegion D)).toReal
  = Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal`,
  i.e. the equality of the two actual hull log-volume readouts (hull task-30's
  exact missing; IUT III Prop. 3.9(i) p. 115, Remark 3.9.5(i); det
  normalization match S3134ThetaHullDetLogVolumeSigned tensor exponent).

Also provided: construction reductions (a genuine proof of a half from the
equality of the corresponding actual numbers) and the composition of the exact
missing with the R1 residual to the actual Step (xi-f) ray
(`S3134FourthTriangleResidual_of_exactMissing`).

No sorry/axiom/arbitrary carrier; the two sides are actual readouts.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointTriangleActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V0 : Type} {I0 : OriginalInput l V0}
variable (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
variable (P : PaperQPilotObjectActual (l := l) (I := I0))

/-! ## 1. The two halves of the last-seam identification -/

/-- q half of the last-seam identification. -/
def S3134LastSeamQHalf : Prop :=
  S3134Step3115QPilotReadout (J := J) = qPilotLogVolumeReading P

/-- Theta half of the last-seam identification. -/
def S3134LastSeamThetaHalf
    (D : S1300HDDHullDetSource I)
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0) : Prop :=
  S3134Step3115ThetaPilotReadout (I := I) D = thetaPilotHullLogVolumeReal C3

/-- The named identification is exactly the conjunction of the two halves. -/
theorem S3134FourthTriangleToC3ReadoutIdentification_iff_halves
    (D : S1300HDDHullDetSource I) :
    S3134FourthTriangleToC3ReadoutIdentification
        (I := I) (J := J) (V0 := V0) (I0 := I0) D C3 P ↔
      S3134LastSeamThetaHalf (I := I) D C3 ∧ S3134LastSeamQHalf (J := J) P := by
  constructor <;> intro h <;> exact h

/-! ## 2. Field-level actual forms -/

/-- q half written with the actual unfolded readouts: the signed fourth-triangle
q readout equals the signed C3 q readout `log ‖P.line.C3.q.q‖`. -/
theorem S3134LastSeamQHalf_iff_actual
    (P : PaperQPilotObjectActual (l := l) (I := I0)) :
    S3134LastSeamQHalf (J := J) P ↔
      -|Real.log (S3134QParameter J)| = Real.log ‖P.line.C3.q.q‖ := by
  unfold S3134LastSeamQHalf S3134Step3115QPilotReadout qPilotLogVolumeReading
  rw [P.signedQPilotLogVolume_eq_log_norm]

/-- q half in magnitude form: equality of the two actual q magnitudes.  Both
signed logarithms are negative, so this is the magnitude form of the q
identification. -/
theorem S3134LastSeamQHalf_iff_magnitudes
    (P : PaperQPilotObjectActual (l := l) (I := I0)) :
    S3134LastSeamQHalf (J := J) P ↔
      |Real.log (S3134QParameter J)| = |Real.log ‖P.line.C3.q.q‖| := by
  rw [S3134LastSeamQHalf_iff_actual]
  have hneg : Real.log ‖P.line.C3.q.q‖ < 0 := by
    rw [← P.signedQPilotLogVolume_eq_log_norm]
    exact P.signedQPilotLogVolume_neg
  have hy : -|Real.log ‖P.line.C3.q.q‖| = Real.log ‖P.line.C3.q.q‖ := by
    rw [abs_of_neg hneg]
    ring
  constructor
  · intro h
    have h' : -|Real.log (S3134QParameter J)| =
        -|Real.log ‖P.line.C3.q.q‖| := by
      rw [h]
      exact hy.symm
    exact neg_inj.mp h'
  · intro h
    have h' : -|Real.log (S3134QParameter J)| =
        -|Real.log ‖P.line.C3.q.q‖| := neg_inj.mpr h
    rw [← hy]
    exact h'

/-- Theta half written with the actual unfolded readouts: the negative HDD
det hull log-volume equals the C3 tensor Haar log-volume of the hull. -/
theorem S3134LastSeamThetaHalf_iff_actual
    (D : S1300HDDHullDetSource I)
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0) :
    S3134LastSeamThetaHalf (I := I) D C3 ↔
      -(D.detData.logVolume
            (S3134ThetaHullRegion (I := I) D)).toReal =
        Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal := by
  unfold S3134LastSeamThetaHalf S3134Step3115ThetaPilotReadout
    S3134ThetaHullLogVolumeSigned S3134ThetaHullLogVolume
    thetaPilotHullLogVolumeReal
  exact Iff.rfl

/-! ## 3. Exact field-level missing and its equivalence to the named
identification -/

/-- Field-level exact missing, q side: equality of the two actual q magnitudes
(the fourth-triangle q parameter and the C3 source completion q norm of the same
fixed input C; IUT I Def. 3.1(b), IUT III Def. 3.8(i) p. 112 / Prop. 3.9(i) p. 115). -/
def S3134LastSeamQMissing
    (J : OriginalInput.{0, uv, upi, umon, ui} l V)
    (P : PaperQPilotObjectActual (l := l) (I := I0)) : Prop :=
  |Real.log (S3134QParameter J)| = |Real.log ‖P.line.C3.q.q‖|

/-- Field-level exact missing, Theta side: equality of the two actual hull
log-volume readouts (HDD det hull vs C3 tensor Haar hull; IUT III Prop. 3.9(i)
p. 115, Remark 3.9.5(i); det normalization match via the S3134 tensor
exponent). -/
def S3134LastSeamThetaMissing
    (D : S1300HDDHullDetSource I)
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0) : Prop :=
  -(D.detData.logVolume (S3134ThetaHullRegion (I := I) D)).toReal =
    Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal

/-- The named last-seam identification is equivalent to the field-level exact
missing (both fields written between actual objects). -/
theorem S3134FourthTriangleToC3ReadoutIdentification_iff_exactMissing
    (D : S1300HDDHullDetSource I) :
    S3134FourthTriangleToC3ReadoutIdentification
        (I := I) (J := J) (V0 := V0) (I0 := I0) D C3 P ↔
      (S3134LastSeamThetaMissing (I := I) D C3 ∧
        S3134LastSeamQMissing (J := J) P) := by
  rw [S3134FourthTriangleToC3ReadoutIdentification_iff_halves]
  constructor
  · intro h
    exact ⟨(S3134LastSeamThetaHalf_iff_actual (I := I) D C3).mp h.1,
      (S3134LastSeamQHalf_iff_magnitudes (J := J) P).mp h.2⟩
  · intro h
    exact ⟨(S3134LastSeamThetaHalf_iff_actual (I := I) D C3).mpr h.1,
      (S3134LastSeamQHalf_iff_magnitudes (J := J) P).mpr h.2⟩

/-! ## 4. Construction reductions: actual number equalities give the halves -/

/-- Construction reduction for the q half: equality of the actual fourth-triangle
q parameter with the actual C3 q norm gives the q readout identification. -/
theorem S3134LastSeamQHalf_of_qParameter_eq
    (P : PaperQPilotObjectActual (l := l) (I := I0))
    (h : S3134QParameter J = ‖P.line.C3.q.q‖) :
    S3134LastSeamQHalf (J := J) P := by
  rw [S3134LastSeamQHalf_iff_actual, ← h]
  have hneg : Real.log (S3134QParameter J) < 0 := by
    rw [h]
    rw [← P.signedQPilotLogVolume_eq_log_norm]
    exact P.signedQPilotLogVolume_neg
  rw [abs_of_neg hneg]
  ring

/-- Construction reduction for the Theta half: equality of the actual HDD det
hull log-volume with the negative C3 tensor Haar log-volume gives the Theta
readout identification. -/
theorem S3134LastSeamThetaHalf_of_volume_eq
    (D : S1300HDDHullDetSource I)
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (h : (D.detData.logVolume
          (S3134ThetaHullRegion (I := I) D)).toReal =
        -Real.log ((actualC3LogShellTensorHaar C3)
          (thetaPilotHull C3)).toReal) :
    S3134LastSeamThetaHalf (I := I) D C3 := by
  rw [S3134LastSeamThetaHalf_iff_actual]
  linarith

/-! ## 5. The actual Step (xi-f) ray from the exact missing and R1 residual -/

/-- The fourth-triangle signed Step (xi-f) ray from the field-level exact missing
plus R1's native-to-C3 same-C readout residual (whose consequence is R1's
unconditional signed regional comparison). -/
theorem S3134FourthTriangleResidual_of_exactMissing
    (D : S1300HDDHullDetSource I)
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P)
    (M : S3134LastSeamThetaMissing (I := I) D C3 ∧
      S3134LastSeamQMissing (J := J) P) :
    S3134Step3115QPilotReadout (J := J) ∈
      hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D) :=
  S3134FourthTriangleResidual_of_R1Identification
    (I := I) (J := J) (T := T) (V0 := V0) (I0 := I0) (mu := mu)
    (C3 := C3) (P := P) D B
    ((S3134FourthTriangleToC3ReadoutIdentification_iff_exactMissing
        (I := I) (J := J) (V0 := V0) (I0 := I0)
        (C3 := C3) (P := P) D).mpr M)

#check S3134FourthTriangleToC3ReadoutIdentification_iff_halves
#check S3134LastSeamQHalf_iff_actual
#check S3134LastSeamQHalf_iff_magnitudes
#check S3134LastSeamThetaHalf_iff_actual
#check S3134FourthTriangleToC3ReadoutIdentification_iff_exactMissing
#check S3134LastSeamQHalf_of_qParameter_eq
#check S3134LastSeamThetaHalf_of_volume_eq
#check S3134FourthTriangleResidual_of_exactMissing

end LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual
