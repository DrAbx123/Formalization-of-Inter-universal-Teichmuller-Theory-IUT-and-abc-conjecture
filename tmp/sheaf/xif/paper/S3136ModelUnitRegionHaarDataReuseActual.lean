import tmp.sheaf.xif.paper.S3136ModelOriginalInputReuseActual

/-! # Stage-4 host: reuse of the prior-art unit-region/Haar data for the model

PRIOR ART (§7.9): SourceUnitRegionHaarDataActual.lean:407 sourceHaarActualUnitRegion,
:416 sourceHaarActualData : I.SourceUnitRegionHaarData, :433 unitRegion theorem,
:441 scaling = 1, :447 nonempty; interface structure at
IQCarrierHaarData.lean:159 (unitRegion, scaling, degreeBound, hull_subset_scaledRegionImage,
unitRegion_logDegree_le, scaling_logDegree_nonpos).

CONSUMER: hull/abc unit-region interface. The model does NOT need a parallel
unit-region definition: the prior-art concrete data is available for any supplied
SourceDefinition31Data; our LGPUnitRegionInterface (native Haar region family) is
mapped onto its fields as data rows.

LABEL: reuse adapter + interface mapping rows. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelUnitRegionHaarDataReuseActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S3136ModelOriginalInputReuseActual

variable {l : PrimeGeFive}

/-- The prior-art concrete unit-region/Haar data for the model original input. -/
def lgpModelUnitRegionHaarData (S : SourceDefinition31Data l)
    (n : ThetaPilotCarrier l) :
    (lgpModelOriginalInput S).SourceUnitRegionHaarData ()
      (sourceHaarActualImageRealization (l := l) S) n :=
  sourceHaarActualData (l := l) S n

/-- Its unit region is the actual source holomorphic hull. -/
theorem lgpModelUnitRegionHaarData_unitRegion (S : SourceDefinition31Data l)
    (n : ThetaPilotCarrier l) :
    (lgpModelUnitRegionHaarData S n).unitRegion =
      sourceHaarActualUnitRegion (l := l) S n :=
  sourceHaarActualData_unitRegion (l := l) S n

/-- Its scaling is the monoid unit. -/
theorem lgpModelUnitRegionHaarData_scaling (S : SourceDefinition31Data l)
    (n : ThetaPilotCarrier l) :
    (lgpModelUnitRegionHaarData S n).scaling = 1 :=
  sourceHaarActualData_scaling (l := l) S n

/-- Its unit region is nonempty. -/
theorem lgpModelUnitRegionHaarData_nonempty (S : SourceDefinition31Data l)
    (n : ThetaPilotCarrier l) :
    (lgpModelUnitRegionHaarData S n).unitRegion.Nonempty :=
  sourceHaarActualData_unitRegion_nonempty (l := l) S n

/-- Mapping rows: our LGPUnitRegionInterface fields <-> prior-art
SourceUnitRegionHaarData fields (data). -/
def lgpUnitRegionInterfaceMapping : List (String × String) :=
  [ ("region (native qVFamTensorBlock family)", "unitRegion : Set (I.ThetaPilotPoint v) -- the actual source holomorphic hull"),
    ("volume (native additive Haar)", "sourceSetVolume (source log-volume of the set)"),
    ("unit-region scaling identity", "scaling = 1 (log-degree 0; does not increase log-volume)"),
    ("regionVolume <= normalizedWeight", "hull_subset_scaledRegionImage + unitRegion_logDegree_le + scaling_logDegree_nonpos (the three prior-art estimate fields)") ]

theorem lgpUnitRegionInterfaceMapping_length : lgpUnitRegionInterfaceMapping.length = 4 := rfl

#check lgpModelUnitRegionHaarData
#check lgpModelUnitRegionHaarData_unitRegion
#check lgpModelUnitRegionHaarData_scaling
#check lgpModelUnitRegionHaarData_nonempty
#check lgpUnitRegionInterfaceMapping_length

end LeanFormal.IUT.XiFPaper.S3136ModelUnitRegionHaarDataReuseActual
end