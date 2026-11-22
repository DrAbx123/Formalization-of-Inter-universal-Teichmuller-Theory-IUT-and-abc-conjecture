# Theta-pilot sign, normalization, and procession range

Date: 2026-10-28. Source analysis only; no Lean compilation and no Lean inequality.

## 1. The source statement and its sign

IUT III, Theorem B, pp.21-22 (extraction lines 1198-1229) and Corollary 3.12,
pp.173-174 (lines 10499-10529) define

  -|log(Theta)| in R union {+infinity}

as the **procession-normalized mono-analytic log-volume of the holomorphic hull
of the union of the possible images** of a Theta-pilot object in the
multiradial representation, relative to the relevant Kummer isomorphisms,
subject to the indeterminacies (Ind1), (Ind2), (Ind3).

The finite value is **non-positive**: it is the negative of the hull
log-volume. The symbol |log(Theta)| is defined as

  |log(Theta)| := -(-|log(Theta)|),

so |log(Theta)| is the positive magnitude. Corollary 3.12 states

  -|log(Theta)| >= -|log(q)|,

which is equivalent to

  |log(Theta)| <= |log(q)|.

This is the opposite direction from the raw theta-value sum formula in the
candidate. In particular, a positive quantity

  G := sum_{b in V_bad} average_j (-log q_{j,b}^2)

cannot itself be -|log(Theta)|: -|log(Theta)| is negative, whereas G is
positive for contracting q values. One must at least pass to -G. But that is
not enough, as the next sections show.

## 2. The procession is over j in F_l^x, not over SignedLabel

The Theta-pilot object of IUT III, Definition 3.8, (i), p.112 (lines
6731-6769) is an object of

  prod_{j in F_l^x} (F_mod^circledast)_j.

The product index is **F_l^x**, not the project's SignedLabel type. The
procession normalization in Theorem B and Corollary 3.12 is explicitly the
average over j in F_l^x (Theorem B, lines 1204-1207; Corollary 3.12, lines
10504-10507). Proposition 3.9, (i), p.116 (lines 7006-7011) confirms that this
normalization is the average over the capsules in the procession.

The local theta values are

  { q_{j,v}^2 }_{j=1,...,l^*},  v in V_bad

(IUT III, pp.16-17, lines 898-902), where l^* = (l-1)/2. These l^* values
represent the theta values up to the mu_{2l}-orbit; the labels themselves range
over the full F_l^x in the Theta-pilot product. The signed-label gadget used by
the project has

  card(SignedLabel l.value) = l,

because it includes 0 and both signs. It is not the paper's F_l^x (cardinality
l-1), and its uniform average is not the paper procession average. The fact
that the candidate coefficient for l = 5 is

  (0^2 + 1^2 + 2^2 + 1^2 + 2^2) / 5 = 10 / 5 = 2

is a signed-label coefficient. It has no direct source justification as the
paper procession coefficient.

## 3. The theta-value log is not the hull log-volume

Even after replacing SignedLabel by F_l^x, the formula

  -|log(Theta)| = - sum_{b in V_bad} average_{j in F_l^x} log(q_{j,b}^2)

is not the paper definition. The reasons are structural:

1. **Hull, not sum.** The paper quantity is the log-volume of the
   **holomorphic hull of the union of possible images** in the multiradial
   representation. A hull log-volume is not the sum of the logarithms of the
   input theta values. It is a nonlinear operation on the image region.
2. **Possible images and indeterminacies.** The union is taken over the
   possible images subject to (Ind1), (Ind2), (Ind3) (Theorem B, lines
   1208-1212; Corollary 3.12, lines 10508-10514). The candidate has no
   possible-image set and no indeterminacies, so it has no hull of possible
   images to measure.
3. **Mono-analytic/Kummer normalization.** The log-volume is mono-analytic and
   relative to the Kummer isomorphisms of Theorem 3.11, (ii). It is not the
   real logarithm of the local theta value q_v^{j^2}.
4. **Theta monoids, not powers.** The theta values enter Definition 3.8, (i)
   through generators of the local splitting monoids
   Psi_perp_{Flgp}(HT)_v, up to torsion. The candidate replaces these by the
   real numbers (baseQReal b)^(j^2); that is a raw q-value model, not the
   monoid/hull object.

Therefore the formula

  globalThetaPilotLogVolume
    = (gaussExponentSum / card(SignedLabel l.value))
      * globalQPilotLogMagnitude

is not a decomposition of the paper -|log(Theta)|. It is a raw theta-value
weighted sum. Its coefficient 2 at l = 5 is a property of that raw sum, not a
paper normalization.

## 4. The q side is also not the paper scalar

The candidate compares against

  globalQPilotLogMagnitude = sum_{b in V_bad} (-log ||baseQ T b||),

i.e. an unweighted bad-place absolute-log sum. Corollary 3.12's -|log(q)| is
the procession-normalized mono-analytic log-volume of the q-pilot image
(Definition 3.8, (i); Theorem B, lines 1213-1217; Corollary 3.12, lines
10516-10521), with the local normalized weights of IUT III, Remark 3.1.1, (ii),
pp.94-95 (lines 5504-5562), and the procession normalization of Proposition
3.9, (i). It is not the raw sum. See GlobalQPilotNormalization.md for the
source normalization analysis.

Thus even if the Theta side were repaired, comparing the candidate to
globalQPilotLogMagnitude would not be the paper comparison.

## 5. Where the l = 5 coefficient comes from and why it is not decisive

For l = 5:

- SignedLabel 5 = { -2, -1, 0, 1, 2 }, card = 5;
- sum of gaussExponents = 0 + 1 + 4 + 1 + 4 = 10;
- coefficient = 10/5 = 2.

If one instead uses F_l^x = {1,2,3,4}, the raw sum of j^2 is 1 + 4 + 9 + 16
= 30, coefficient 30/4 = 7.5. Neither coefficient is a paper hull
normalization. The paper -|log(Theta)| is not obtained by averaging the raw
theta-value logs over any of these label sets; it is the hull log-volume of the
multiradial possible images. The coefficient 2 is therefore a diagnostic of the
raw-sum model, not a contradiction with the source: the source quantity was
never that sum.

## 6. Correct normalizations

The correct objects and normalizations are:

1. **Theta-pilot object**:
   object of prod_{j in F_l^x} (F_mod^circledast)_j determined by the local
   splitting-monoid generators at all v in V_bad (Definition 3.8, (i)).
2. **Possible images**:
   the images of this object in the multiradial representation of Theorem
   3.11, (i), subject to (Ind1), (Ind2), (Ind3).
3. **Hull**:
   the holomorphic hull of the union of the possible images in the
   j-th IQ capsule.
4. **Log-volume**:
   the procession-normalized mono-analytic log-volume: packet-normalized local
   log-volumes averaged over the capsules in the procession (Proposition 3.9,
   (i), (ii)), with the normalized weights of Remark 3.1.1, (ii).
5. **Final average**:
   average over j in F_l^x, explicitly as in Theorem B and Corollary 3.12.
6. **Sign**:
   -|log(Theta)| is the negative of this hull log-volume; |log(Theta)| is its
   positive magnitude. The inequality -|log(Theta)| >= -|log(q)| is equivalent
   to |log(Theta)| <= |log(q)|.

None of these steps is a sum of raw theta-value logs over SignedLabel.

## 7. Verdict

The candidate's error is not a single sign flip and not a single missing
division. The error is at the object level:

- it uses SignedLabel (the project's l-element signed set, including 0) instead
  of the paper's label product over F_l^x;
- it uses the raw local theta values q_v^{j^2} instead of the local
  splitting-monoid generators and the multiradial possible images;
- it takes the sum of local theta-value logs instead of the log-volume of the
  holomorphic hull;
- it omits (Ind1), (Ind2), (Ind3), the Kummer isomorphisms, and the
  mono-analytic normalization;
- it takes a positive raw magnitude as -|log(Theta)|, whose source value is
  negative.

Consequently the formula

  globalThetaPilotLogVolume
    = (gaussExponentSum / card(SignedLabel l.value))
      * globalQPilotLogMagnitude

is not the paper -|log(Theta)|. At l = 5 its coefficient 2 is a raw
signed-label theta-sum coefficient, not a source procession coefficient. The
source comparison with -|log(q)| cannot be judged from this formula.

## 8. References

- IUT III, Definition 3.8, (i), p.112: extraction lines 6731-6769.
- IUT III, Introduction, pp.16-17: lines 880-908.
- IUT III, Theorem B, pp.21-22: lines 1198-1229.
- IUT III, Corollary 3.12, pp.173-174: lines 10499-10529.
- IUT III, Proposition 3.9, (i), p.116: lines 7006-7011.
- IUT III, Remark 3.1.1, (ii), pp.94-95: lines 5504-5562.
- IUT II, Introduction, pp.2-3: lines 69-108.
- IUT II, Remark 2.5.1, pp.72-73: lines 4356-4396.
- IUT II, Corollary 4.10, (i), pp.158-159: lines 10473-10515.
- Project candidate: tmp/sheaf/xif/paper/GlobalThetaPilotLogVolumeActual.lean,
  globalThetaPilotLogVolume_eq.
- Project concrete signed procession:
  tmp/sheaf/xif/paper/PaperSignedHullSignedActual.lean,
  c3ThetaSignedProcession.
