import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S3134FourthJointCompositeActual
import tmp.sheaf.xif.paper.S3134Step3115To312Actual
import tmp.sheaf.xif.paper.S3132Task30ThetaHalfActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3132Task30ThetaHalfActual

namespace LeanFormal.IUT.XiFPaper.S3132UniformFactorComparisonComponentActual

universe u v uv upi umon ui

/-!
# task-38: the uniform HDD-factor / C3-packet comparison — construction and minimal residual

**Component, not a paper object.**  Owner: hull.  Consumers: task-30's
`MissingFourthTriangleThetaHalfReadout`; shehdd's fourth-triangle chain; lattice R1.

(a) **Constructed (no missing datum):** the HDD source carries the uniform
local-field data `D.localEquiv v : (i : Fin D.rank) → D.E i ≃+* (oneColumnStructure).localField v`
(an `S1300HDDHullDetSource` field, the `S1356UniformLocalEquiv` shape).  Its
underlying function gives the actual transport `hddTo1ColumnFunction`; only the
underlying function is needed for hull transport.

(b) **Missing (shrunk to one field-level object):**
`MissingC3PacketUniformComparisonData` with `indexEquiv : Fin D.rank ≃ C3.tensorIndex`
and `fiberEquiv : (v) (i) → oneColumnStructure.localField v ≃+* C3LogShellFiber C3 (indexEquiv i)`,
`Prop` form `MissingC3PacketUniformComparison := Nonempty Data`.

**Why not constructible.**  `oneColumnStructure.localField v = Completion v` is
the completion of `Q` at the finite place `v`, while
`C3LogShellFiber C3 j = CommonPrimeCompletion (c3LogShellPlace C3 j)` is the
completion of `I.initial.arithmetic.Fmod` at the selected C3 tensor place.  A
uniform ring equivalence exists only when each C3 tensor place is a degree-one
completion over the rational place below it with matching rational primes; the
source place data certifying this (`placeToMod` with bijectivity, residue
characteristic and degree-one comparison) is **not exposed by `OriginalInput`**
(`SourceDefinition31DualContractAlignment.lean:88`: no record projection
`SourceInitialThetaData -> SourceDefinition31Data`; and the all-place record
trivializes by cardinality alone, see the negative result in
`S3132PrimeStripC3AllPlaceComparisonComponent`).  Pages: IUT III, Definition 3.1
(pp. 30-40); Theorem 3.11 (pp. 160-162); IUT IV, Theorem 1.10 proof (pp. 26-27);
Remark 3.9.5, (i), (ii) (pp. 158-160).

(c) **Constructed given (b):** `hddToC3Function` and the transported hull
`hddToC3Hull` (image of the actual `LocalFieldProductHull.hull` of the actual HDD
image at the actual SHE output object).

(d) **Remaining normalization residual (task-30 step (3)).**  The paper's signed
readout is the degree-normalized log-volume `arithmeticTupleNormalizedLogVolume`
(V-form = (1/finrank)(log mu(S) - log mu(O_hol)), `O_hol = arithmeticTupleCanonicalUnitReference`;
IUT III, Proposition 3.9, (i), p. 115), while shehdd's
`S3134Step3115ThetaPilotReadout` is the raw signed HDD determinant log-volume
(`S3134ThetaHullLogVolumeSigned`) and `thetaPilotHullLogVolumeReal` is `Real.log`
of the raw C3 Haar measure.  **Convention mismatch confirmed by shehdd:** the
S3134 chain does not use the V-form, so the target identity is a genuine
normalization residual, not implied by transport or Haar-mass equality.  The
sharper paper-faithful target: `thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu`
(shehdd's canonical rooted V-form readout) via `S3134Step3115_canonicalQC_le_thetaPilot`.
-/

/-- **Constructed actual step (1a):** underlying transport function of the
uniform HDD local-field identification (actual `D.localEquiv` data). -/
noncomputable def hddTo1ColumnFunction
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) (D : S1300HDDHullDetSource ID)
    (v : NumberField.FinitePlace ℚ) :
    ((i : Fin D.rank) → D.E i) → ((i : Fin D.rank) → (oneColumnStructure).localField v) :=
  fun x i => D.localEquiv v i (x i)

/-- **Minimal exact missing datum (step (1b)).**  Uniform index and ring-level
factor-field comparison of the HDD local factors with the C3 packet fibers. -/
structure MissingC3PacketUniformComparisonData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID) where
  indexEquiv : Fin D.rank ≃ C3.tensorIndex
  fiberEquiv : (v : NumberField.FinitePlace ℚ) → (i : Fin D.rank) →
    (oneColumnStructure).localField v ≃+* C3LogShellFiber C3 (indexEquiv i)

/-- The `Prop` form of the minimal exact missing datum. -/
def MissingC3PacketUniformComparison
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID) : Prop :=
  Nonempty (MissingC3PacketUniformComparisonData ID C3 D)

/-- **Constructed given the minimal missing comparison (step (1c)):** transport
of the HDD factor product into the C3 log-shell fiber product, indexed by the
HDD rank through the uniform index comparison. -/
noncomputable def hddToC3Function
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (M : MissingC3PacketUniformComparisonData ID C3 D)
    (v : NumberField.FinitePlace ℚ) :
    ((i : Fin D.rank) → D.E i) →
      ((i : Fin D.rank) → C3LogShellFiber C3 (M.indexEquiv i)) :=
  fun x i => M.fiberEquiv v i (hddTo1ColumnFunction ID D v x i)

/-- The C3-packet transport of the actual HDD hull image (the actual
`LocalFieldProductHull.hull` of the actual HDD image at the actual SHE output
object, pushed along the constructed product transport). -/
noncomputable def hddToC3Hull
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (M : MissingC3PacketUniformComparisonData ID C3 D)
    (v : NumberField.FinitePlace ℚ) :
    Set ((i : Fin D.rank) → C3LogShellFiber C3 (M.indexEquiv i)) :=
  hddToC3Function ID C3 D M v ''
    @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField
      (D.image (S3134SHEOutputObject (I := ID)))

/-- **Normalization residual (step (3)).**  Matching the actual fourth-triangle
Theta readout (raw signed HDD determinant log-volume) with the raw C3 Haar
reading is a genuine normalization residual: the paper's signed readout is the
degree-normalized V-form (IUT III, Proposition 3.9, (i), p. 115; e = 1 passage is
task-13's `QVFamNormalizedNormCompatibility`).  Owner: hull/mainline; not claimed
here.  Sharper paper-faithful form:
`thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu`. -/
structure MissingThetaLogNormalization
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID) : Prop where
  normalized_readout_eq :
    S3134Step3115ThetaPilotReadout (I := ID) D = thetaPilotHullLogVolumeReal C3

/-- **Reduction theorem.**  The task-30 Theta-half residual follows from the two
named inputs: the transport comparison (step (1b)) and the normalization identity
(step (3)). -/
theorem missingThetaHalf_of_transport_and_normalization
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (M : MissingC3PacketUniformComparison ID C3 D)
    (N : MissingThetaLogNormalization ID C3 D) :
    MissingFourthTriangleThetaHalfReadout (I := ID) (I0 := I2) C3 D :=
  ⟨N.normalized_readout_eq⟩

#check hddTo1ColumnFunction
#check MissingC3PacketUniformComparisonData
#check MissingC3PacketUniformComparison
#check hddToC3Function
#check hddToC3Hull
#check MissingThetaLogNormalization
#check missingThetaHalf_of_transport_and_normalization

end LeanFormal.IUT.XiFPaper.S3132UniformFactorComparisonComponentActual

end