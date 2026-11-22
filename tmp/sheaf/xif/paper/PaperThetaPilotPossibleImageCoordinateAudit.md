# Theta-pilot possible image: source coordinates vs value-layer surrogate

Scope: source-text and current-tree audit only. No fake hull or equality is
introduced.

## 1. Source coordinate structure

IUT III, proof of Corollary 3.12 (iut3.txt:10535-10586), writes

    n,◦U_{j,vQ} ⊆ I_Q(S^±_{j+1}; n,◦D^⊣_{vQ})

for j ∈ |F_l| and vQ ∈ VQ. Here:

* S^±_{j+1} = {0,1,...,j} is the label container of the tensor packet
  (iut3.txt:560-566, 598-604);
* the tensor packet is the tensor product, over the elements of S^±_{j+1}, of
  the direct sums of the log-shells associated to the corresponding
  prime-strips (iut3.txt:580-604);
* the theta values {q_v^{j^2}} generate the splitting monoids of LGP-monoids
  that act on these tensor packets (iut3.txt:610-621, 899-907).

Thus a possible image n,◦U_{j,vQ} is a region in a tensor product indexed by
S^±_{j+1} (with log-shell/integral structure), not a function on the paper
labels F_l^x whose every coordinate is the same scalar.

## 2. Current project object

In PaperThetaPilotCarrierActual.lean:

    PaperThetaPilotPoint := PaperThetaPilotCarrier → Multiplicative Real
    paperThetaPilotPointAt q j :=
      fun _ => Multiplicative.ofAdd (Real.log (paperThetaValue q j))

So the point is constant on every F_l^x coordinate: every label receives the
same value log(q^{j^2}). This is a diagonal/value-layer surrogate. It is not
the tensor-packet region n,◦U_{j,vQ} of the source, and its hull cannot be used
to infer the paper's coordinatewise possible-image structure or equality with
a q-pilot object.

The earlier sourceThetaPilotPoint in SourceImageHull.lean has the same
constant-on-all-components shape (constantThetaPilotPoint), so the issue is
not limited to the paper carrier wrapper: the value-layer realization is
diagonal.

## 3. Correct tuple-level candidate

PaperThetaPilotPossibleImageCoordinateActual.lean constructs the better
value-layer tuple candidate

    paperThetaPilotTuplePoint q j :
      PaperThetaPilotCarrier → Multiplicative Real
    paperThetaPilotTuplePoint q j k =
      if k = j then ofAdd(log(thetaValue q j)) else 1.

It proves:

* paperThetaPilotTuplePoint_self: at k = j, the value is the theta value;
* paperThetaPilotTuplePoint_other: at k ≠ j, the value is 1;
* paperTuplePossibleImageSet := Set.range (paperThetaPilotTuplePoint q);
* paperThetaPilotTuplePoint_mem.

This removes the diagonal/constant defect at the value-layer level. It is
still only a value-layer model of the source tensor packet. It does not assert
that the source region n,◦U_{j,vQ} is this tuple, and it does not prove any
hull equality or inequality.

## 4. Exact remaining gap

The full source object is a region in the tensor product over S^±_{j+1} with
log-shell/integral structure, not a single tuple over F_l^x with one real
scalar per label. The exact missing data are recorded in the Lean file as

    structure PaperThetaPilotTensorPacketImageGap where
      tensorLabel : Type
      imageRegion : Set (tensorLabel → Multiplicative Real)
      labelProjection : tensorLabel → PaperThetaPilotCarrier
      not_diagonal : Prop

and the obstruction is

    PaperThetaPilotTensorPacketImageObstruction :=
      Nonempty (PaperThetaPilotTensorPacketImageGap ...)

This is an exact gap, not a fabricated tensor region. In particular, the
constant paperThetaPilotPointAt hull and the sourceThetaPilotPoint hull should
not be used to derive the paper equality. Only after constructing the actual
S^±_{j+1}-indexed tensor packet, the actual log-shell regions, and the actual
action of the theta values can one pass to the holomorphic hull and its
log-volume.

## 5. Consequence

* The current paperThetaPilotPointAt q j = fun _ => log(thetaValue q j) is a
  diagonal value-layer surrogate, not the paper's possible image.
* The corrected tuple candidate puts theta at the j-th F_l^x coordinate and 1
  elsewhere; it is the right value-layer shape but still not the full
  S^±_{j+1}-indexed tensor-packet region.
* No equality or hull sup should be inferred from the current constant hull.
* The exact missing source object is the S^±_{j+1}-indexed tensor packet with
  its log-shell/integral regions and theta-value action.
