# Audit: PaperThetaHullEqQPilotActual and PaperLabelHullHaarComputed

Date: 2026-10-29. Analysis only.

## Verdict

INVALID as a paper-faithful Theta-pilot hull construction.  It is a
constant-tuple / diagonal surrogate.  It must not be used to derive
hull = q-pilot equality.

## What the file actually constructs

In PaperThetaPilotCarrierActual:

  PaperThetaPilotPoint = (ZMod l.value)^x -> Multiplicative Real,

  paperThetaPilotPointAt q j
    = fun _ => Multiplicative.ofAdd (log (paperThetaValue q j))

  paperPossibleImageSet q = Set.range (paperThetaPilotPointAt q).

Every possible image is the SAME theta value in every F_l^x component.  It is a
constant/diagonal tuple, not a paper Theta-pilot possible image with the j-th
F_l^x component carrying q_v^{j^2} (or the corresponding F_l^x-orbit).

The hull paperThetaPilotHull q is the generic monoid hull of these diagonal
points in the function-space monoid.  Its Haar volume is a measure-theoretic
object on a diagonal subset; it is not the paper hull of the union of possible
images in the F_l^x-indexed tensor packet.

## Why PaperLabelHullHaarComputed is not justified

PaperLabelHullHaarComputed q asserts

  (paperThetaPilotHaar (paperLabelHull q 1)).toReal
    = (paperThetaValue q 1) ^ card(SourceVolumeIndex l).

Problems:

1. The exponent card(SourceVolumeIndex l) is the size of
   ThetaPilotCarrier l x SignedLabel l.value,
   i.e. (lStar l.value + 1) * l.value.  For l = 5 this is 3 * 5 = 15.
   It is NOT the number of F_l^x labels (which is l - 1 = 4), and not the
   rank/dimension of the F_l^x value carrier.  Using it as a hull-volume
   exponent is a surrogate identification.

2. paperLabelHull q 1 is the hull of a single constant tuple point.  The Haar
   measure on the function space is an additive translation Haar measure; a
   singleton has measure zero, and a monoid hull of a point is not in general a
   measurable scale region whose measure is q^{card}.  No source theorem or
   actual computation supports that equality.

3. The equality is tailored to make the log-volume equal to
   card(SourceVolumeIndex) * log(q), which is exactly the q-side scalar.  That
   is circular: it assumes the desired hull=q-pilot equality through the Haar
   computation field.

4. PaperLabelHullCopiesSame is also not paper-faithful.  At label j the
   constant-tuple scalar is q^{j^2}, so the log-volumes differ by j^2.  For
   l = 5, averaging over units gives the 5/2 factor, not 1.  The file's
   conditional equality cannot hold for the actual paper theta values.

## Correct paper-side object required

For each label j in F_l^x, the possible image in the multiradial representation
is obtained by placing the theta value q_v^{j^2} in the j-th F_l^x component
(or by applying the actual F_l^x permutation action to a fixed component), not
by copying one value to every component.  The hull must then be formed in the
actual F_l^x-indexed tensor packet, with the actual lambda*O scaling and unit
region, and only after that may the F_l^x procession average be taken.

The missing actual objects are:

- actual F_l^x component indexing of the possible images;
- actual per-label possible-image points in the tensor packet;
- actual lambda*O hull on that packet;
- actual normalized Haar/packet log-volume of that hull;
- actual F_l^x average of the hull log-volumes.

## Consequence

- Mark PaperThetaHullEqQPilotActual's PaperLabelHullHaarComputed and
  PaperLabelHullCopiesSame invalid as paper-faithful objects.
- Do not use the conditional theorem
  paperHullThenAverage_eq_qPilotLocalSignedScalar as evidence for hull=q-pilot.
- Do not continue the hull=q-pilot equality from this surrogate.
- A corrected construction needs the F_l^x-component possible image and actual
  tensor-packet hull above; no fake equality should replace it.
