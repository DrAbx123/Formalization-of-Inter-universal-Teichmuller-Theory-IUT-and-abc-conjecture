# S1028: actual link from sourceQ

Date: 2026-10-30. Link actual; hlink exact identification.

## Canonical actual object

s1028Oa := s1009CanonicalOa I C1 C2 C3.

hC3 is actual: s1009Canonical_hC3.
hQ is sourceQ: s1009HQ_iff_sourceQ.

## Link from sourceQ

s1028Link hsrc : PaperXiFSourceLink (concreteO I) P C3, for
hsrc : S1009SourceQIdentification I C3 = (sourceQPilotSignedLog I.initial =
localSignedLog C3.q).

Thus sourceQ alone constructs the actual link; no fake link field.

s1028Link_actual : Nonempty (PaperXiFSourceLink ...) from sourceQ.

## hlink

S1028HLink hsrc := (s1028Link hsrc).link_identification.

s1028HLink_iff_theta:
  S1028HLink hsrc <-> thetaSourceComparison s1028Oa P.

So the link identification is the actual theta source comparison
(P.procession.average <= -Oa.signedQPilotLogVolume), not fabricated.

## Inclusion / exact minimum

s1028Inclusion hsrc hlink : PaperXiFInclusion (concreteO I) P C3.
S1028ExactMinimum hsrc := S1028HLink hsrc.

Exact list: sourceQ for the link, plus the link-identification proof hlink for
the inclusion.  hlink is not derivable from sourceQ alone; no fake.
