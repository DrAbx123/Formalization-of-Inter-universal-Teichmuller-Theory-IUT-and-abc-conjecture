/-!
# S3139: vendor treasure-survey record (promachina Stage1) for the first-triangle/route batch

Per Lead directive (repo treasure trove), surveyed
vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/Iut/Stage1
(separate lake project; SOURCE REFERENCE ONLY, not importable).  Findings adapted
in this batch: (file:line, name)
* Iut/Stage1/IUTStage1ConstructedTheorem311.lean:772
  structure IUTIIIMultiradialProcession; :797 IUTIIIMultiradialProcession.ofM2;
  :837-841 constructed multiradial procession from source.m2
  -> adapted as @SourceMultiradialProcessionConsumer (S3139MultiradialProcessionConsumerActual).
* Iut/Stage1/IUTStage1Gaussian.lean:3580
  structure LGPSplittingMonoidTensorPacketAction (fields packet, actedTensorPacketLogVolume);
  :3629 theorem actedTensorPacketLogVolume_eq_original_plus_generators
  -> adapted as the linear-readout scalar law
     @sourceLGP_linearReadout_action (S3139TensorPacketScalarLogVolumeActual).
* Iut/Stage1/IUTStage1SourceCore.lean:1012 IUTStage1ProcessionNormalizedLogVolume;
  :1299 IUTStage1ProcessionTensorPacketLogVolume; :1392
  IUTStage1ProcessionFiberTensorPacketLogVolume (+ namespace laws around :1406-1459)
  -> template for the tensor-packet log-volume readout interface; our
     log-volume consumers stay in S3131/S3134 streams (no new numeric data here).
* Iut/Stage1/IUTStage1ConstructedTheorem311.lean:33 structure IUTIIIProcessionChoice,
  :71 ind1Act, :79 ind2Act, :87 ind3Lift with laws ind1Act_add, ind2Act_add etc.
  -> confirms our S3138 procession carrier design (Ind1/Ind2 actions, Ind3 one-sided
     upper-semi); no code change needed.
* Iut/Stage1/IUTStage1SourceCore.lean:4040 IUTStage1ProcessionState.
* Also referenced by TOOL-INVENTORY H: CorollarySchema.lean (Corollary312Inequality/
  ComparisonData/thetaPilot/qPilot), IUTStage1IUTIVAlgebra.lean (GenEll),
  IUTStage1FrobenioidShift.lean (qPilotRegion) — route Cor 3.12 side; not needed for
  the first-triangle copy-action closure.

REUSE POLICY: vendor is not importable; the adapted items above are re-proved in
our stream with our objects.  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorSurveyActual

/-- Survey findings: (vendor file:line, name, our adapted declaration). -/
def vendorSurveyFindings : List (String × String × String) :=
  [ ("IUTStage1ConstructedTheorem311.lean:772", "IUTIIIMultiradialProcession",
      "SourceMultiradialProcessionConsumer"),
    ("IUTStage1Gaussian.lean:3580", "LGPSplittingMonoidTensorPacketAction",
      "sourceLGP_linearReadout_action"),
    ("IUTStage1Gaussian.lean:3629", "actedTensorPacketLogVolume_eq_original_plus_generators",
      "sourceLGP_linearReadout_action"),
    ("IUTStage1SourceCore.lean:1392", "IUTStage1ProcessionFiberTensorPacketLogVolume",
      "log-volume readout interface template"),
    ("IUTStage1ConstructedTheorem311.lean:71", "ind1Act/ind2Act/ind3Lift",
      "S3138 procession carrier (no change)") ]

end LeanFormal.IUT.XiFPaper.S3139VendorSurveyActual
