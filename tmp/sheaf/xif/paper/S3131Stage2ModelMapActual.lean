import tmp.sheaf.xif.paper.S3131PaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-! # S3131 task-29: light same-C model map (native T <-> Stage-2 C3/P)

Component, not a paper object: exact shape of the same-C model identification
between mainline native T (weighted bad family) and lattice Stage-2 (C3, P).
Fields M0-M3 are exact Prop placeholders (Missing, page refs below); M5a'/M5b'
are the two concrete cross-carrier readout equalities.  Consumer: lattice
S3137NativeToC3SameCReadoutActual via nativeToC3Identification_of_modelMap.
Page refs: M0 IUT I Def 3.1; M1 IUT I Def 3.1(b),(e), IUT III Prop 3.4(ii);
M2 IUT I Example 3.2(iv), IUT III Def 3.8(i) p.112; M3 IUT II Remark 2.5.1(i);
M5 IUT IV Prop 1.4(i), IUT III Prop 3.9(i) p.115, Cor 3.12 10324-10353.
No carrier, no surrogate, no sorry/axiom. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3131Stage2ModelMapActual

universe u

variable {l : PrimeGeFive} {V : Type}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData I)
variable (P : PaperQPilotObjectActual I)

/-- Exact residual shape (weakest correct variant A). -/
structure S3131Stage2ModelMapGlobal where
  arithmeticModelMatch : Prop
  badTensorIndexMatch : Prop
  qParameterMatch : Prop
  thetaValueMatch : Prop
  qReadoutMatch : qPilotLogVolumeReading P = S3131PaperRegionalQ T mu
  hullReadoutMatch : thetaPilotHullLogVolumeReal C3 = S3131PaperRegionalHull T mu

/-- Lattice's NativeToC3SameCReadoutIdentification from the model map. -/
theorem nativeToC3Identification_of_modelMap
    (M : S3131Stage2ModelMapGlobal T mu C3 P) :
    NativeToC3SameCReadoutIdentification (l := l) T mu C3 P := by
  unfold NativeToC3SameCReadoutIdentification
  exact ⟨M.qReadoutMatch, M.hullReadoutMatch⟩

/-- Exact residual shape (per-place variant B). -/
structure S3131Stage2ModelMapPerPlace where
  arithmeticModelMatch : Prop
  badTensorIndexMatch : Prop
  qParameterMatch : Prop
  thetaValueMatch : Prop
  weightTotal : Prop
  qReadoutMatch : Prop
  hullReadoutMatch : Prop

#check S3131Stage2ModelMapGlobal
#check S3131Stage2ModelMapPerPlace
#check nativeToC3Identification_of_modelMap

end LeanFormal.IUT.XiFPaper.S3131Stage2ModelMapActual

end
