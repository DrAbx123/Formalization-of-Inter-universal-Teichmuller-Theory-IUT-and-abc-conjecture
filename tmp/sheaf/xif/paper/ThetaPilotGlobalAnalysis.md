# Global Theta-pilot log-volume: source formula, dependencies, and the q=1/5 signed hull

Date: 2026-10-28. Source analysis only; no Lean compilation, no Lean inequality.

## 1. Source object

### 1.1 Theta-pilot object

IUT III, Definition 3.8, (i), p.112 (extraction lines 6731-6769):

- the Theta-pilot object is the object of

  prod_{j in F_l^x} (F_mod^circledast)_j

  determined by any collection, indexed by v in V_bad, of generators up to
  torsion of the splitting monoids Psi_perp_{Flgp}(HT)_v;

- the q-pilot object is the object of the global realified Frobenioid
  C_Delta^vdash of IUT II, Corollary 4.10, (i), determined by the collection of
  q_v for v in V_bad.

Thus the Theta-pilot object has **two independent index directions**:

1. the label direction j in F_l^x (the product over j);
2. the bad-place direction v in V_bad (the local monoids at each v).

It is not a single theta value and not a single local packet. IUT III, pp.16-17
(lines 888-908) describes it as the arithmetic divisor determined by the zero
locus of the collection of theta values

  { q_{j,v}^2 }_{j=1,...,l^*},  v in V_bad.

IUT II, Introduction, pp.2-3 (lines 69-108) gives the local theta function at
v and the values q_v^{j^2}; IUT II, Remark 2.5.1, pp.72-73 (lines 4356-4396)
identifies the theta values with the mu_{2l}-orbit of q_v^{j^2}. These local
values are the input to the monoids in Definition 3.8, (i).

### 1.2 -|log Theta| is a global hull log-volume

IUT III, Theorem B, pp.21-22 (lines 1198-1229) and Corollary 3.12,
pp.173-174 (lines 10499-10529):

- -|log(Theta)| is the **procession-normalized mono-analytic log-volume** of
  the **holomorphic hull** of the **union of the possible images** of a
  Theta-pilot object in the multiradial representation;
- the possible images are subject to the indeterminacies (Ind1), (Ind2),
  (Ind3);
- the procession normalization is the average over j in F_l^x
  (Theorem B explicitly says "where the average is taken over j in F_l^x";
  Corollary 3.12 repeats this in the parenthetical at lines 10504-10507);
- the construction uses the relevant Kummer isomorphisms of Theorem 3.11;
- the value lies in R union {+infinity}; the finite value is the paper's
  negative Theta-pilot log-volume.

The definition of procession normalization is in Proposition 3.9, (i), p.116
(lines 7006-7011): log-volumes on products of capsules in a procession are
normalized by taking the average over the capsules. So the outer operation is

  average over j in F_l^x   of   (mono-analytic log-volume of a hull),

not a sum over j and not a single theta packet.

## 2. Global formula

The source does not display a closed formula in the q_v alone. The structurally
correct formula is the following.

For each v in V_bad and each label j in F_l^x, let

  Theta_{j,v}

be the local Theta-value data determined by the theta values q_{j,v}^2 (up to
the mu_{2l}-orbit) and by the splitting monoid Psi_perp_{Flgp}(HT)_v. Let

  Theta-pilot = (Theta_{j,v})_{j in F_l^x, v in V_bad}

be the object of prod_j (F_mod^circledast)_j described in Definition 3.8, (i).
Let

  pi_j : Theta-pilot -> IQ(S^pm_{j+1}; D^vdash_{v_Q})

be the j-th component of the multiradial representation (Theorem 3.11, (i),
(a)), considered up to (Ind1), (Ind2), (Ind3). Let

  U_{j,v_Q}

be the holomorphic hull, in the j-th IQ capsule, of the union of the possible
images of the j-component at v_Q. Let

  mu_log^{proc}(U_j)

be the procession-normalized mono-analytic log-volume of the j-component, i.e.
the packet-normalized log-volume averaged over the capsules in the procession
(Proposition 3.9, (i), (ii)). Then the paper's global quantity is

  -|log(Theta)|
    = average_{j in F_l^x} [ mu_log^{proc}(U_j) ],

with the hull of the union of possible images and the (Ind1)/(Ind2)/(Ind3)
indeterminacies understood. Equivalently, in the finite case,

  -|log(Theta)|
    = (1 / |F_l^x|) * sum_{j in F_l^x} mu_log^{H}(U_j),

where mu_log^{H} is the hull log-volume after the packet/procession
normalization, and U_j is the holomorphic hull of the possible j-images.

This formula makes explicit the two dependencies that matter:

1. **all v in V_bad**, because the Theta-pilot object is determined by the
   collection of the local monoids/theta values at every bad place;
2. **all j in F_l^x**, because the object is a product over j, and the final
   log-volume is averaged over the procession.

It is not the log-volume of one local theta packet.

### 2.1 Dependence on actual q_v/theta data

The actual data entering -|log(Theta)| are:

- for every v in V_bad, the local q-parameter q_v and its 2l-th root/theta
  normalization (IUT I, Definition 3.1, (b); IUT II, pp.2-3 and Remark 2.5.1);
- the theta values q_v^{j^2} for every j in F_l^x, up to the mu_{2l}-orbit;
- the local splitting monoids Psi_perp_{Flgp}(HT)_v and their generators
  (Definition 3.8, (i));
- the arithmetic holomorphic structure of the 1-column and the 0-column
  (Theorem 3.11, (i); Corollary 3.12 proof, Step (xi));
- the relevant Kummer isomorphisms (Theorem 3.11, (ii));
- the multiradial representation and the possible images under (Ind1),
  (Ind2), (Ind3);
- the holomorphic hull and the mono-analytic log-volume normalization
  (Remark 3.1.1, (ii); Proposition 3.9, (i), (ii)).

The value is therefore a function of the **full V_bad theta/q family and the
full label product**, not of one local Gaussian q.

## 3. The concrete signed hull at q = 1/5

### 3.1 What the current concrete object is

The project's concrete signed hull is built from

  c3ThetaSignedProcession (actualSignedC3 D),

where actualSignedC3 is c3WithSourceTheaterTheta: a source-theater C3 whose
theta packet is the concrete Gaussian packet at q = 1/5, with one uniform
finite procession over SignedLabel l.value. Its values are

  value j = -Real.log (C3.thetaPacket.scale j),

and its weights are the uniform weights 1/card(SignedLabel l.value).

Its average is the actual signed Gaussian average

  (c3ThetaSignedProcession actualSignedC3).average
    = log 5 * (gaussExponentSum l / card(SignedLabel l.value)).

For l = 5 this is

  log 5 * (10 / 5) = 2 log 5.

The corresponding signed hull log-volume used by PaperSignedHull is the
negative of this average, and the PaperSignedHull hull log-volume field is the
C6 IQ hull log-volume identified with this average.

### 3.2 Is it paper-faithful?

No, not as the global -|log(Theta)|. It is a **local Gaussian packet signed
average**, not the global paper quantity. The differences are structural:

1. **Only one local q.** The concrete C3 uses the single source-theater
   Gaussian q = 1/5. The paper Theta-pilot object uses the whole collection
   q_v at all v in V_bad; the q = 1/5 packet is one local/theta-side value.
2. **No V_bad sum/index.** The concrete average ranges only over the labels
   j in SignedLabel l.value. It has no index over v in V_bad and no collection
   of local monoids at all bad places.
3. **No multiradial possible images.** The concrete object is the raw signed
   procession average of the C3 packet. The paper -|log(Theta)| is the
   procession-normalized log-volume of the **holomorphic hull of the union of
   possible images** in the multiradial representation, subject to (Ind1),
   (Ind2), (Ind3).
4. **No Kummer/arithmetic-holomorphic structure.** The paper value is relative
   to the Kummer isomorphisms and the arithmetic holomorphic structure of the
   1-column/0-column. The concrete average uses the C3 theta packet and the C6
   Haar normalization only.
5. **Sign normalization.** The paper -|log(Theta)| is a negative finite
   number (or +infinity for the hull). The concrete
   c3ThetaSignedProcession.average is a positive magnitude (2 log 5 at
   l = 5); its negative is the signed hull log-volume. Thus the concrete
   positive average is not the paper -|log(Theta)| itself, but at best its
   magnitude under a local sign convention.

The concrete q = 1/5 packet can be a **local Gaussian component** or a
normalization test for one place, but it is not the global Theta-pilot
log-volume. Calling its average -|log(Theta)| is not paper-faithful.

## 4. What would be paper-faithful

A paper-faithful construction would need:

- the actual V_bad-indexed family of local theta monoids/values
  Theta_{j,v}, not a single q = 1/5 packet;
- the product object over j in F_l^x of Definition 3.8, (i), and its
  multiradial representation;
- the union of possible images under (Ind1), (Ind2), (Ind3);
- the holomorphic hull in each IQ capsule and the mono-analytic log-volume
  with the Remark 3.1.1, (ii) weights;
- the procession average over j in F_l^x;
- the relevant Kummer isomorphisms and arithmetic holomorphic structure.

Only after these objects exist does the formula of Section 2 determine
-|log(Theta)|. The concrete signed hull at q = 1/5 supplies none of the
V_bad-indexed data and none of the multiradial hull data, so it cannot be
identified with the global paper quantity.

## 5. Relation to the q-pilot comparison

The paper comparison is

  -|log(Theta)| >= -|log(q)|    (Corollary 3.12, lines 10527-10529).

Here -|log(q)| is the procession-normalized mono-analytic log-volume of the
q-pilot image, built from the q_v at all v in V_bad (Definition 3.8, (i);
Theorem B, lines 1213-1217; Corollary 3.12, lines 10516-10521). The concrete
signed hull average at q = 1/5 is not the left-hand side of this comparison,
and the unweighted sourceQPilotSignedLog is not the right-hand side in general
(see GlobalQPilotNormalization.md). Any comparison using the q = 1/5 average
must be described as a local Gaussian model, not as the paper inequality.

## 6. Bottom line

1. The paper -|log(Theta)| is the procession-normalized mono-analytic
   log-volume of the holomorphic hull of the union of possible Theta-pilot
   images in the multiradial representation, averaged over j in F_l^x and
   subject to (Ind1), (Ind2), (Ind3).
2. It depends on the full V_bad-indexed collection of local q_v and theta
   values q_v^{j^2}, on all labels j in F_l^x, on the local splitting monoids,
   the Kummer isomorphisms, and the arithmetic holomorphic structure.
3. The concrete signed hull at q = 1/5 uses one local Gaussian packet and the
   uniform SignedLabel procession; its average is
   log 5 * (gaussExponentSum / card(SignedLabel l.value)).
4. That concrete average is a local Gaussian signed magnitude, not the paper
   global -|log(Theta)|. It is not paper-faithful for the global Theta-pilot
   log-volume.

## 7. References

- IUT II, Introduction, pp.2-3: extraction lines 69-108.
- IUT II, Remark 2.5.1, pp.72-73: lines 4356-4396.
- IUT II, Corollary 4.10, (i), p.158-159: lines 10473-10515.
- IUT III, Definition 3.8, (i), p.112: lines 6731-6769.
- IUT III, Introduction, pp.16-17: lines 880-908.
- IUT III, Theorem B, pp.21-22: lines 1198-1229.
- IUT III, Corollary 3.12, pp.173-174: lines 10499-10529.
- IUT III, Proposition 3.9, (i), p.116: lines 7006-7011.
- IUT III, Remark 3.1.1, (ii), pp.94-95: lines 5504-5562.
- Project concrete signed procession:
  tmp/sheaf/xif/paper/PaperSignedHullSignedActual.lean, c3ThetaSignedProcession.
- Project concrete signed average formula:
  tmp/sheaf/xif/paper/SignedAverageBoundActual.lean,
  actualSignedC3_signedAverage_eq_log5_mul_sum_div_card.
