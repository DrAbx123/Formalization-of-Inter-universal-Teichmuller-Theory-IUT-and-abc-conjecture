/-!
# S3139: vendor treasure-survey part 2 — FrobenioidShift/SourceCore structures (data only)

More findings from vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/Iut
(source reference only, not importable), relevant to first-triangle/route work:

* Iut/Stage1/IUTStage1FrobenioidShift.lean:19564 def qPilotRegion (and :20094,
  :20277, :20678, :24126 further qPilotRegion defs in target packages);
  :20711/:24160 qPilotRegion packaged into target Chared Hodge determinant
  possible-image hull-det obligations -> route q-pilot region templates; ours is
  built in the qpilot/mainline streams (S3131/S3133/S3137 qTheta bridge).
* Iut/Stage1/IUTStage1FrobenioidShift.lean:6000 structure ProcessionTransport;
  :927 structure ProcessionPrimeStripId -> procession transport/prime-strip id
  templates (our S3138 procession carrier + S3139 capsule ids).
* Iut/Stage1/IUTStage1FrobenioidShift.lean:92
  structure IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice ->
  "conjugate choice absorbed by one-column log-volume compatibility": the vendor
  analogue of our C3 convention-independence (polyIso vs procession convention);
  supports the comparison-neutral region entry used in this stream.
* Iut/Stage1/IUTStage1FrobenioidShift.lean:11776/12910/14077
  NonarchimedeanRealifiedFrobenioidLogKummerPacket(Source/Entry/EntrySource) ->
  realified frobenioid log-Kummer packet structures; stage4/lattice territory
  (Frobenioid log-Kummer packets), useful reference for the LGP/Φ-input work.
* Iut/Stage1/IUTStage1FrobenioidShift.lean:34266
  structure Theorem311MultiradialFinitePlaceCThetaAudit -> Theorem 3.11
  multiradial finite-place CTheta audit template (first-triangle finite-place).
* Iut/Stage1/IUTStage1SourceCore.lean:1012/1137/1154/1299/1392 procession
  normalized/label-averaged/weighted-label-averaged/tensor-packet/fiber log-volume
  structures -> adapted: SourceProcessionTensorPacketLogVolume (batch 1) and
  SourceLabelAveragedLogVolume / SourceWeightedLabelAveragedLogVolume (this batch).

REUSE POLICY: vendor is not importable; adapted items are re-proved with our
objects.  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorSurveyPart2Actual

/-- Part-2 survey findings: (vendor file:line, name, our adaptation/status). -/
def vendorSurveyPart2 : List (String × String × String) :=
  [ ("IUTStage1FrobenioidShift.lean:19564", "qPilotRegion",
      "route q-pilot region template (qpilot/mainline streams)"),
    ("IUTStage1FrobenioidShift.lean:6000", "ProcessionTransport",
      "procession transport template (S3138/S3139)"),
    ("IUTStage1FrobenioidShift.lean:927", "ProcessionPrimeStripId",
      "prime-strip id template (S3139 capsule ids)"),
    ("IUTStage1FrobenioidShift.lean:92", "OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice",
      "vendor analogue of C3 convention-independence (comparison-neutral regions)"),
    ("IUTStage1FrobenioidShift.lean:11776", "NonarchimedeanRealifiedFrobenioidLogKummerPacketSource",
      "stage4/lattice reference (frobenioid log-Kummer packets)"),
    ("IUTStage1FrobenioidShift.lean:34266", "Theorem311MultiradialFinitePlaceCThetaAudit",
      "first-triangle finite-place audit template"),
    ("IUTStage1SourceCore.lean:1137/1154", "LabelAveraged/WeightedLabelAveraged procession log-volume",
      "SourceLabelAveragedLogVolume / SourceWeightedLabelAveragedLogVolume (this batch)") ]

end LeanFormal.IUT.XiFPaper.S3139VendorSurveyPart2Actual
