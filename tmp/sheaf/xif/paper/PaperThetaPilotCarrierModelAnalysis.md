# Paper Theta-pilot carrier model: multiradial IQ vs F_l^x value profile

Date: 2026-10-28. Source analysis only; no Lean compilation and no Lean inequality.

## 1. Question

The project has two carriers:

- the paper value-profile model

  PaperThetaPilotPoint = F_l^x -> Multiplicative Real,

  used in PaperThetaPilotCarrierActual;

- the global IQ completion-packet tensor

  GlobalIQAmbient C3 j = ArithmeticPacketTensor (literalIQPlaces C3 j),

  used in GlobalIQHullInterfaceActual.

The question is where the paper Theta-pilot hull actually lives, and whether the
q-pilot image lives on the same carrier.

## 2. The source multiradial carrier

### 2.1 Tensor packets indexed by S^pm_{j+1}

IUT III, Introduction, pp.10-14 (extraction lines 560-709) constructs the
multiradial representation as follows. For each

  * in S^pm_{j+1} = {0,1,...,j},  j = 0,...,l^*,

and each v_Q in V_Q, one forms

- the direct sum of the log-shells associated to the D^vdash-prime-strip
  labeled by * at the v in V over v_Q;
- the tensor product, over the elements * in S^pm_{j+1}, of these direct sums.

The resulting collection of tensor products, indexed by v_Q in V_Q, is the
**tensor packet** associated to the labeled prime-strips. This is carried out
for mono-analytic D^vdash-prime-strips (IUT III, Proposition 3.2). The
resulting containers are written

  IQ(S^pm_{j+1}; D^vdash_{v_Q})

in the Theta-pilot log-volume discussion (IUT III, Corollary 3.12 proof, lines
10550-10578; see also lines 9345-9360).

Thus the paper Theta-pilot hull lives in a **tensor packet of log-shells on
labeled D^vdash-prime-strips**, indexed by a capsule label set S^pm_{j+1} and a
place v_Q. It is not a function on F_l^x.

### 2.2 The Theta-pilot object itself

IUT III, Definition 3.8, (i), p.112 (lines 6731-6769):

- the Theta-pilot object is an object of

  prod_{j in F_l^x} (F_mod^circledast)_j,

  determined by generators of the local splitting monoids
  Psi_perp_{Flgp}(HT)_v at v in V_bad;

- the q-pilot object is an object of the global realified Frobenioid C_Delta^vdash
  of IUT II, Corollary 4.10, (i), determined by the q_v at v in V_bad.

The product index F_l^x is the **pilot-object label index**; the capsule tensor
packets are indexed by S^pm_{j+1}. These are related by the evaluation/label
constructions, but they are not the same index set: S^pm_{j+1} has j+1
elements, and j runs from 0 to l^*, whereas F_l^x has l-1 elements.

### 2.3 The possible-image subsets and hull

Corollary 3.12 proof, lines 10550-10578:

  n,circ U_{j,v_Q} subset IQ(S^pm_{j+1}; n,circ D^vdash_{v_Q})

is the union, over the possible images of a Theta-pilot object relative to the
Kummer isomorphisms and subject to (Ind1), (Ind2), (Ind3), of the images in the
multiradial representation. The holomorphic hull is then taken in each
IQ(S^pm_{j+1}; ...) capsule.

Consequently:

  Theta-pilot hull at label/capsule j and place v_Q
    lives in IQ(S^pm_{j+1}; n,circ D^vdash_{v_Q}),
    a tensor packet of log-shells,

and the final -|log(Theta)| is the procession-normalized average over the
labels/capsules of the log-volumes of these hulls (Theorem B, lines 1198-1229;
Corollary 3.12, lines 10499-10529).

## 3. Where the q-pilot image lives

Theorem B, lines 1213-1217, and Corollary 3.12, lines 10516-10521:

- -|log(q)| is the procession-normalized mono-analytic log-volume of the image
  of a q-pilot object in the **same multiradial representation**;
- the q-pilot image is not subject to (Ind1), (Ind2), (Ind3);
- the q-pilot object itself is an object of the global realified Frobenioid
  C_Delta^vdash (Definition 3.8, (i); IUT II, Corollary 4.10, (i)).

So the answer to "same carrier?" is:

- **same multiradial ambient family**: both the Theta-pilot hull and the q-pilot
  image are represented in the common IQ(S^pm_{j+1}; D^vdash_{v_Q}) tensor
  packets, which is exactly what makes the comparison in Corollary 3.12
  meaningful;
- **not the same pilot object**: the q-pilot is an object of C_Delta^vdash
  determined by the q_v family; the Theta-pilot is an object of the product
  over j in F_l^x of the theta monoids. They are different objects represented
  in a common ambient container.

The common carrier is therefore the IQ tensor-packet family, not a single
carrier of the form F_l^x -> Real.

## 4. The paper value-profile model

The project carrier

  PaperThetaPilotPoint = F_l^x -> Multiplicative Real

is a real-valued profile model. It was built from:

- the theta values q_v^{j^2} at v in V_bad;
- a point that places one theta value at every F_l^x label;
- the generic value-realized holomorphic hull SourceImageHull.holomorphicHull.

It is useful as a value-level surrogate, but it is not the paper carrier. In
the paper:

1. the carrier is a tensor packet of log-shells on labeled D^vdash-prime-strips,
   IQ(S^pm_{j+1}; D^vdash_{v_Q}), not F_l^x -> Multiplicative Real;
2. the labels are the capsule labels S^pm_{j+1} and the F_l^x labels of the
   Theta-pilot product, not a single function-space index;
3. the theta values are embedded in the splitting monoids of LGP-monoids and
   the Kummer theory, not represented as raw real powers q_v^{j^2};
4. the possible images include the (Ind1)/(Ind2)/(Ind3) indeterminacies;
5. the hull is a holomorphic hull in the IQ tensor capsule, with the
   mono-analytic log-volume, not a value-realized hull in a real function
   space.

Therefore the value-profile model loses the actual IQ/log-shell/tensor-packet
structure. It cannot be the paper Theta-pilot carrier.

## 5. The project GlobalIQAmbient model

GlobalIQAmbient C3 j = ArithmeticPacketTensor (literalIQPlaces C3 j) is closer
to the paper carrier:

- it is an actual tensor packet of completion packets;
- it has an actual unit region (tensor integral region), actual additive Haar
  measure, actual compactness, and actual Haar log-volume;
- its index is Fin (j+1) x C3.tensorIndex, i.e. a capsule-like factor index
  times the C3 tensor places.

It is still not the literal paper IQ(S^pm_{j+1}; D^vdash_{v_Q}):

1. the paper carrier uses D^vdash-prime-strips and their log-shells
   I(D_v), not merely the C3 completion-packet tensor places;
2. the paper capsule labels are S^pm_{j+1} with its permutation
   indeterminacies, not the fixed C3 tensor index;
3. the paper carrier includes the arithmetic holomorphic structure and the
   Kummer isomorphisms, which are not part of the bare completion tensor;
4. the actual place selection of C3 is not identified with the paper D^vdash
   prime-strip places.

Thus GlobalIQAmbient is an actual completion-packet approximation to the IQ
carrier, but it is not the literal paper carrier either. This is why no actual
equivalence with the value-profile model exists in the tree: both project
carriers are models, and the paper carrier is a third, more structured object.

## 6. Is there an actual equivalence?

No actual equivalence

  GlobalIQAmbient C3 j  ~  F_l^x -> Multiplicative Real

is constructed in the tree, and none is expected from the source. The two
models have different index sets and different mathematical structure:

- GlobalIQAmbient: tensor packet indexed by completion places / capsule
  factors;
- PaperThetaPilotPoint: function space on the theta-label group F_l^x.

An equivalence would require at least:

1. an actual identification of the capsule index Fin (j+1) x C3.tensorIndex
   with the paper's D^vdash-prime-strips and S^pm_{j+1} labels;
2. an actual place map from the C3 tensor places to the paper v in V over v_Q;
3. an identification of the log-shell/tensor-packet unit region with a region
   in the function-space model;
4. compatibility with the Kummer isomorphisms and the (Ind1)/(Ind2)/(Ind3)
   indeterminacies.

None of these is in the tree. Constructing an equivalence by choosing a basis
or an arbitrary bijection would not be the paper object; it would fabricate the
missing structure.

## 7. Correct model statement

The correct statement is:

- the Theta-pilot object is an object of
  prod_{j in F_l^x} (F_mod^circledast)_j;
- its possible images live in the IQ tensor packets
  IQ(S^pm_{j+1}; D^vdash_{v_Q}) for the capsule labels S^pm_{j+1};
- the Theta-pilot hull is the holomorphic hull in those IQ tensor packets;
- the q-pilot image lives in the same multiradial IQ tensor-packet family, but
  the q-pilot object itself is an object of the global realified Frobenioid
  C_Delta^vdash;
- -|log(Theta)| is the procession-normalized mono-analytic log-volume of the
  hull, averaged over the capsule labels, subject to (Ind1)/(Ind2)/(Ind3);
- -|log(q)| is the procession-normalized log-volume of the q-pilot image in the
  same multiradial representation.

The F_l^x -> Multiplicative Real value-profile and the bare completion-tensor
GlobalIQAmbient are both simplified models. Neither is the paper carrier, and
no equivalence between them is constructed or assumed.

## 8. References

- IUT III, Introduction, pp.10-14: extraction lines 560-709 (tensor packets,
  multiradial representation, (Ind1)/(Ind2)/(Ind3)).
- IUT III, Definition 3.8, (i), p.112: lines 6731-6769.
- IUT III, Theorem B, pp.21-22: lines 1198-1229.
- IUT III, Corollary 3.12, pp.173-174: lines 10499-10529.
- IUT III, Corollary 3.12 proof, pp.174-175: lines 10535-10578
  (n,circ U_{j,v_Q} subset IQ(S^pm_{j+1}; n,circ D^vdash_{v_Q})).
- IUT III, Proposition 3.2 / Proposition 3.9: tensor packets and log-volumes.
- IUT II, Corollary 4.10, (i), pp.158-159: C_Delta^vdash / F_Delta^vdash.
- Project value carrier:
  tmp/sheaf/xif/paper/PaperThetaPilotCarrierActual.lean.
- Project IQ carrier:
  tmp/sheaf/xif/paper/LiteralIQCarrierConstructionActual.lean and
  tmp/sheaf/xif/paper/GlobalIQHullInterfaceActual.lean.
- Project equivalence obstruction:
  tmp/sheaf/xif/paper/PaperGlobalIQCarrierEquivActual.lean.
