# S968: final Cor312 from tensor inequality

Date: 2026-10-30. Inequality + source/link conditional assembly.

## Inputs

Tensor data D : forall b, FinalLTensorLogVolumeData T b.
Per-b:
* S957ThetaImageDenseInQPilot T b (D b);
* 0 < (D b).measure (qPilotPaperImageInLValued T b);
* (D b).measure (paperTensorHull T b (D b)) < top.

Source/link:
* link : PaperXiFSourceLink O P C3;
* hlink : link.link_identification;
* links : finite IPL/SHE/APT evidence for s968Inclusion.

## Actual result

s968Inclusion link hlink : PaperXiFInclusion O P C3.

paperCor312_of_tensorInequality:
  tensor hypotheses
  -> link -> hlink -> links
  -> tensorPacketPaperWeightedInequality D
     and Cor312Conclusion of the assembled certificate.

Proof:
* tensor inequality is S962.tensorPacketPaperWeightedInequality_of_perB;
* Cor312 is paperAssembly_cor312Conclusion with the explicit source link and
  hlink.

S968TensorHypotheses bundles the three tensor conditions.

No equality, no scaling data, no PaperGap equality.
