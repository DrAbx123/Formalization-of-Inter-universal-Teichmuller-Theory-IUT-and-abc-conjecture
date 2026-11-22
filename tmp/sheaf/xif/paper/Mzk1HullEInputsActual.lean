import tmp.sheaf.xif.paper.Hull13H7Ob9ComparisonConsumerActual
import tmp.sheaf.xif.paper.Hull09H5GapsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: H5 O^x|O(-)^-1|hull volume|H7 Ob9 Ind3|Cor312 -> hits Hull09H5GapsActual (O^x-stabilization PROVED, hull=closure PROVED, det-tensor bookkeeping PROVED, hull ray PROVED; 2 class-B named), Hull10H7Ob9ConsumerActual (wiring consumer PROVED), Hull12Ob9BoundTransferActual (upper-bound transfer PROVED), Hull13H7Ob9ComparisonConsumerActual (comparison consumer PROVED; deep arbitrary-iterate Ob9 class-B).

# Mzk1HullEInputsActual — conditional assembly: H5/H7 named inputs -> GenEll (Cor312) intermediate

Problem E / A398.  All H5/H7 NAMED deep inputs are explicit structure parameters; the
assembly PROVES the GenEll-needed intermediate conclusion (Cor 3.12 hull+det
conclusion + base possible-image upper bound + the PROVED H5 class-A components) and
passes the named inputs through for the full paper/ABC consumer.  No closure claim.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullEInputsActual

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual
open LeanFormal.IUT.XiFPaper.Indet06H7Ob9WiringActual
open LeanFormal.IUT.XiFPaper.Hull10H7Ob9ConsumerActual
open LeanFormal.IUT.XiFPaper.Hull12Ob9BoundTransferActual
open LeanFormal.IUT.XiFPaper.Hull13H7Ob9ComparisonConsumerActual
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}

variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **H5 named deep inputs (class B).**  The two H5 items that remain paper inputs:
(i) the full O(-)^{-1} normalization on the arithmetic line bundle; (ii) the
hull <= image-volume inequality.  They are explicit parameters of the conditional
assembly (never free fields of a claimed-precise witness). -/
structure HullEH5NamedInputs (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- class-B named: full paper O(-)^{-1} normalization on the arithmetic line bundle. -/
  oInverseNormalization : Prop
  /-- class-B named: hull <= image-volume inequality (tree report R9/R10: not a
  formal consequence of the value layer). -/
  hull_le_image_volume : Prop

/-- **H7/Ob9 named deep input (class B):** arbitrary log-link iterate independence
of the comparison (deep Ob9). -/
structure HullEH7NamedInput (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- class-B named: the comparison is independent of the chosen log-link iterate. -/
  arbitraryIterateIndependence : Prop

/-- H5 proved class-A components packaged for the consumer: O^x-stabilization and
hull = submonoid closure(possible images, scaling units). -/
def HullEH5ProvedComponents (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  ∀ (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l),
    I.sourceScalingUnits v ⊆ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
    I.sourceHolomorphicHull v R n =
      Submonoid.closure (I.possibleThetaPilotImageSet v R n ∪ I.sourceScalingUnits v)

/-- H5 proved components hold (class A; consumes Hull09 tree reuse). -/
theorem hullE_h5_proved_components (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    HullEH5ProvedComponents (l := l) I := by
  intro v R n
  exact ⟨hull09_scalingUnits_subset_hull I v R n, hull09_hull_eq_closure I v R n⟩

/-- **GenEll intermediate conclusion** needed by the Cor312->ABC conditional interface:
Cor 3.12 hull+det conclusion + base possible-image upper bound + the H5 class-A
components + the H5/H7 named deep inputs passed through. -/
def HullEGenEllIntermediateConclusion
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9ComparisonInputs (l := l) M I)
    (h5 : HullEH5NamedInputs (l := l) I) (h7 : HullEH7NamedInput (l := l) I) : Prop :=
  Cor312HullDetConclusion M In.consumer.hull.theta ∧
    (∀ z : ℝ, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.consumer.base) → z ≤ In.bound) ∧
    HullEH5ProvedComponents (l := l) I ∧
    h5.oInverseNormalization ∧ h5.hull_le_image_volume ∧
    h7.arbitraryIterateIndependence

/-- **Conditional assembly (Problem E):** from the H7/Ob9 comparison consumer inputs
(class A chain: Hull10 wiring + Hull12 transfer + Hull13 comparison) together with the
H5/H7 NAMED deep inputs, derive the GenEll intermediate conclusion.  Every parameter
is consumed; the named inputs are explicit (conditional, no closure). -/
theorem hullE_genEll_intermediate
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9ComparisonInputs (l := l) M I)
    (h5 : HullEH5NamedInputs (l := l) I) (h7 : HullEH7NamedInput (l := l) I)
    (h5o : h5.oInverseNormalization) (h5v : h5.hull_le_image_volume)
    (h7i : h7.arbitraryIterateIndependence) :
    HullEGenEllIntermediateConclusion (l := l) M I In h5 h7 := by
  obtain ⟨hcor, hbound⟩ := hull13_h7ob9_comparison (M := M) I In
  exact ⟨hcor, hbound, hullE_h5_proved_components I, h5o, h5v, h7i⟩

/-- The Cor 3.12 hull+det conclusion alone, as consumed by the Cor312->ABC conditional
interface. -/
theorem hullE_cor312
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9ComparisonInputs (l := l) M I) :
    Cor312HullDetConclusion M In.consumer.hull.theta :=
  (hull13_h7ob9_comparison (M := M) I In).1

/-- Inventory rows: H5/H7 proved vs named after Problem E assembly. -/
def hullEInputRows : List (String × String × String) :=
  [ ("H5 O^x-stabilization (scaling units in hull)", "A", "REUSED-PROVED Hull09.hull09_scalingUnits_subset_hull (tree CardHullRealGeometryReduction:94)")
  , ("H5 hull = closure(images, scalings)", "A", "REUSED-PROVED Hull09.hull09_hull_eq_closure (tree :108)")
  , ("H5 det-tensor bookkeeping + hull log-volume ray", "A", "REUSED-PROVED Hull09.hull09DetTensorBookkeeping / hull09_ray_mem_iff (HullDeterminantLogVolumeReduction:483/501)")
  , ("H5 full O(-)^{-1} normalization on arithmetic line bundle", "B-NAMED", "explicit parameter HullEH5NamedInputs.oInverseNormalization (field of the arithmetic line bundle not formalized)")
  , ("H5 hull <= image-volume inequality", "B-NAMED", "explicit parameter HullEH5NamedInputs.hull_le_image_volume (tree report R9/R10)")
  , ("H7/Ob9 wiring (Ind1/Ind2 invariance, Ind3 one-sided)", "A", "REUSED-PROVED Hull10.hull10_h7ob9_consumer (Indet06 wiring)")
  , ("Ob9 upper bound transfer (Ind3 iterate -> base)", "A", "REUSED-PROVED Hull12.hull12_upperBound_transfer")
  , ("H7/Ob9 one-sided comparison consumer", "A", "REUSED-PROVED Hull13.hull13_h7ob9_comparison")
  , ("deep Ob9: arbitrary log-link iterate independence of the comparison", "B-NAMED", "explicit parameter HullEH7NamedInput.arbitraryIterateIndependence (not formalized)")
  , ("GenEll Cor312->ABC conditional intermediate", "CONDITIONAL", "PROVED hullE_genEll_intermediate (conditional on H5/H7 named inputs)") ]

theorem hullEInputRows_length : hullEInputRows.length = 10 := rfl

#check HullEH5NamedInputs
#check HullEH7NamedInput
#check HullEH5ProvedComponents
#check HullEGenEllIntermediateConclusion
#check hullE_genEll_intermediate
#check hullE_cor312
#check hullEInputRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullEInputsActual
end