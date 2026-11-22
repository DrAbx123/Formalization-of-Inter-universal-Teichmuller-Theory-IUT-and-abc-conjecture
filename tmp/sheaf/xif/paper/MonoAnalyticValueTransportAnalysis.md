# Mono-analytic value transport: analysis and exact gap

## 1. Question

The previous layer requested

  ValueMonoidToCompletion v :
    I.ValueMonoidAt 0 0 v ->* CommonPrimeCompletion (P.stripPlace v).

The question is whether this completion-valued monoid map is actually part of
the paper's multiradial representation, or an artifact of the simplified
LiteralIQAmbient construction.

## 2. Paper-side reading

In IUT III, the multiradial representation and the log-Kummer correspondence
operate on

* the value monoid / Frobenioid value data Mon v of the prime strip;
* its degree/log map to Multiplicative Real;
* the mono-analytic log-shell carrier I(D_v), a compact topological module;
* tensor packets of log-shells.

The comparison between the Frobenius-like value data and the etale/mono-analytic
log-shell side is the log-Kummer correspondence.  It is not a monoid
homomorphism from the abstract value monoid Mon v to the p-adic completion
field.  In particular:

* Mon v is the value monoid of the prime strip, not a submonoid of the
  completion;
* the log map used by the mono-analytic representation is the local logarithm
  on units / the log-shell module, not an algebra map into the completion;
* the tensor packet is a packet of log-shell regions, not a pointwise product
  of completion-valued theta-pilot points.

Therefore the requested ValueMonoidAt -> CommonPrimeCompletion monoid map is
not justified by the paper.  It is an artifact of asking the simplified
LiteralIQAmbient (a tensor of completion packets) to receive the global
Theta-pilot point carrier directly.

## 3. What the paper actually needs

The correct transport is mono-analytic:

  value data / degree  ->  log-shell region  ->  tensor packet of log-shells.

It is a transport of regions/modules, not a pointwise completion-valued monoid
map.  The relevant actual objects already present in the tree are:

* SourceImageHull.ThetaPilotPoint,
  sourceThetaPilotPoint, possibleThetaPilotImageSet,
  sourceHolomorphicHull;
* I.logDegreeAt : ValueMonoidAt 0 0 v -> Real,
  and the source degree map Mon v ->* Multiplicative Real;
* PrimeStripLogShellActual.actualC3LogShell,
  the actual integral log-shell at each C3 tensor place;
* C3LogShellTensorPacketActual / LiteralIQCarrierConstruction:
  actual tensor packets and tensor integral regions;
* MonoAnalyticLogShellCompactCarrier:
  the compact topological-module API for pre-log-shell/log-shell,
  with logMap, scaling, compactness and containment.

What is missing is the actual source theorem

  value data/degree  ->  the specific mono-analytic log-shell carrier
  (and its tensor packet),

with the log-Kummer compatibility.  The repository has interfaces and
calibrations for the log-shell carrier, but not the paper's concrete
value-to-log-shell representation.

## 4. Consequence for the IQ ambient

The GlobalThetaPilotCarrier -> LiteralIQAmbient embedding is therefore the
wrong interface target if it is required to be induced by a monoid map to
completions.  The correct replacement is one of:

1. keep the global Theta-pilot carrier as a value-side object and compare it to
   the tensor log-shell carrier through a mono-analytic representation map
   (not a completion-valued monoid map); or
2. replace the ambient by the actual mono-analytic log-shell/tensor carrier
   before constructing the global hull interface.

Either way, ValueMonoidToCompletion should not be manufactured.  A trivial or
arbitrary monoid map to the completion would be fake and would also be unrelated
to the paper's log-Kummer correspondence.

## 5. Actual objects written in this layer

The accompanying Lean file MonoAnalyticValueTransportActual.lean constructs:

* the actual real log-degree profile of the global Theta-pilot carrier,
  using I.logDegreeAt (source prime-strip value data);
* the exact missing target type for a mono-analytic log-shell representation
  map (value monoid -> a MonoAnalyticLogShellCompactCarrier module),
  recorded as an obstruction, not inhabited.

No completion-valued monoid map is constructed.

## 6. Exact missing fields (paper-level)

1. A concrete mono-analytic log-shell carrier for each v / C3 tensor place,
   with the actual local log and compact topological-module structure.
2. The actual value/data-to-log-shell representation map, compatible with the
   source degree/log data.
3. The tensor-packet assembly of those log-shells and the comparison with the
   global LiteralIQAmbient (or a replacement of that ambient).
4. The log-Kummer compatibility of the representation with the Theta-link.

These are genuine source obligations; not an invitation to insert an arbitrary
completion-valued homomorphism.
