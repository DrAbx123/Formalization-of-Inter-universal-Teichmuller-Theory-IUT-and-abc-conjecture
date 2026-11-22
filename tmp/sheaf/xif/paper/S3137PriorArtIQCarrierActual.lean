import LeanFormal.IUT.Audit.Status

/-! # S3137: prior-art inventory — IQCarrierConcreteModel concrete IQ hull/interface chain

Lead-directed mapping of LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierConcreteModel.lean
(the concrete real-line IQHullLogVolumeInterface with hunit/hsplit/hptfin/
hweightvol/hpoint and the epsilonComparison/Additive assembly) to the model-route
clauses.  Source-only references; data file.  No registry edit.
-/

namespace LeanFormal.IUT.XiFPaper.S3137PriorArtIQCarrierActual

/-- IQCarrierConcreteModel declarations -> model-route clauses. -/
def S3137PriorArtIQCarrier : List (String × String × String) :=
  [ ("concrete IQHullLogVolumeInterface", "IQCarrierConcreteModel.lean:193 iqCarrierModelInterface (Real carrier, logDegree id, scaling 0, unitRegion Iic 0, hull Iic 0)", "REUSE as concrete model skeleton (model-route (i)); TOY Real carrier, not paper evidence"),
    ("unit-region/log-volume facts", "IQCarrierConcreteModel.lean:112/118/130/136/145/166 iqCarrierModelUnitRegion_logDegree_le, _ScaleShift_image_unitRegion, _image_Iic_zero, _LogVolume_Iic_zero, _union, _union_le", "REUSE"),
    ("F4 clause inputs: hunit", "IQCarrierConcreteModel.lean:303/315 iqCarrierModel_hunit_unitRegion, iqCarrierModel_hunit_degreeBound", "REUSE: F4(b) hunit chain on the concrete model"),
    ("F4 clause inputs: hweightvol/hsplit/hptfin/hpoint", "IQCarrierConcreteModel.lean:346/358/373/386 iqCarrierModel_hweightvol, _hsplit, _hptfin, _hpoint", "REUSE: all four gap inputs constructed on the model"),
    ("epsilonComparison assembly", "IQCarrierConcreteModel.lean:413/431 iqCarrierModel_epsilonComparison, iqCarrierModel_epsilonComparisonAdditive", "REUSE: Cor312 comparison fields (V1 + V2 additive) on the model"),
    ("point weight/height/shell point", "IQCarrierConcreteModel.lean:220/225/230/235 iqCarrierModelPointWeight, _PointHeight, _LogShellPoint, _UnitShellPoint", "REUSE: logShellPoint datum on the model; paper-route field (c) shape"),
    ("dictionary facts + non-universality", "IQCarrierConcreteModel.lean:446/458/473/495/531/559 iqCarrierModel_weightDictionary, _pointHeightDictionary, _no_singleMap_bothDictionaries, _arithmeticWeight_unbounded, _hmem_hweightvol_incompatible, _not_hweightvol_unitShellPoint", "REUSE: dictionary is a hypothesis, not universal (consistent with Cor312GapDictionaryLayer)"),
    ("model-point triple checks", "IQCarrierConcreteModel.lean:251/267/282/290/328 iqCarrierModel_radical_six, _pointWeight_triple_123, _pointHeight_triple_123, _LogShellPoint_triple_123_not_mem, _LogVolume_region_eq", "REUSE: concrete sanity witnesses") ]

theorem S3137PriorArtIQCarrier_length : S3137PriorArtIQCarrier.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.S3137PriorArtIQCarrierActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: prior-art inventory IQCarrierConcreteModel chain. -/
def S3137PriorArtIQCarrierRecord : Obligation :=
  { id := "INDEX.PRIOR-ART.iq-carrier-concrete-model"
    source := "IQCarrierConcreteModel.lean:81-559; IQCarrierRealizationAlignment.lean; IQCarrierHaarData.lean; SourceImageHull.lean"
    status := VerificationStatus.interface
    note := "PRIOR ART (concrete model chain): the concrete IQHullLogVolumeInterface (Real carrier) with logDegree/scaling/unitRegion/hull and logVolume facts, the F4-clause inputs hunit/hsplit/hptfin/hweightvol/hpoint, and the epsilonComparison/epsilonComparisonAdditive Cor312 assembly are ALREADY PROVED in IQCarrierConcreteModel.lean. Reuse for model-route clause (i)/(ii)/(iii) and F4 clause inputs; this concrete model is a TOY Real carrier, not paper evidence for general ABC (input-fidelity note stands)."
    dependsOn := ["S3137PriorArtIQCarrierActual"] }

end LeanFormal.IUT.Audit
