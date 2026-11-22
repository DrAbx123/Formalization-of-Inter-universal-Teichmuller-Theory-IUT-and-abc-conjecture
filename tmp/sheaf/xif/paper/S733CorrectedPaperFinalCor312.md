# S733: corrected P final conditional Cor312

Date: 2026-10-30. Replaces S676's s663 surrogate theta side by the corrected
paper hull P (S725/S721 conditional object).

## Corrected P

S733CorrectedHullLog P T b :=
  P.signedHullLogVolume = -paperPerBThetaHullLog (l := l0) T b.

s733_signed_log states this explicitly.

## Conditional source link

s733SourceLink uses S725.s725PaperXiFSourceLink with:
* hP: corrected signed log;
* hident: the four source identifications;
* hqpaper: S669QPilotLogVolumeEqPaper O C3;
* link_identification and link_implies_inclusion to membership in the signed
  hull ray of P.

s733Inclusion adds hlink.

## Final conditional Cor312

s733_finalCor312 constructs PaperXiFInclusion O P C3 and calls
paperAssembly_cor312Conclusion with actual finite IPL/SHE/APT links:

  Cor312Conclusion
    ((paperCertificate (I := paperXiFInput J)).toContract
      (paperSignedLinkEvidence (I := paperXiFInput J) links)).

No fake q/link/evidence; P is explicit as required, not the S663 surrogate.
