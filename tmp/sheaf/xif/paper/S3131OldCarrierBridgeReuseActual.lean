import tmp.sheaf.xif.paper.S3136OldCarrierBridgeExistsActual

/-! # S3131 reuse: OLD CARRIER BRIDGE EXISTS (S2586 IQHullLogVolumeInterface) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131OldCarrierBridgeReuseActual

def S3131OldCarrierBridge : List (String × String) :=
  [ ("S2586IQHullLogVolumeInstantiationActual:32 S2586IQHullLogVolumeInterface T b", "IQHullLogVolumeInterface (qVFamTensorBlock T b): logVolume := Measure.addHaar, unitRegion := arithmeticTupleCanonicalUnitReference, hull := rootNormHull, scaleShift := id; fields proved -> CARRIER BRIDGE EXISTS (not missing)"),
    ("S3136OldCarrierBridgeExistsActual", "lgpNativeIQInterface (4 decls top-level API) -> REUSE"),
    ("honesty", "old S2722_bridgeS2586 target Cor312ToABCBridgeInterface = ABC-strength calibration => conditional ABC-strength statement, NOT discharge; old hval REFUTED; hweightvol open gap-1; hpoint degenerate (singleton-null) do not use") ]

theorem S3131OldCarrierBridge_length : S3131OldCarrierBridge.length = 3 := rfl

-- #check (prior-art name to verify later): lgpNativeIQInterface

end LeanFormal.IUT.XiFPaper.S3131OldCarrierBridgeReuseActual
end