# Audit: the 2.5 coefficient is average-first, not paper hull-first

Date: 2026-10-29. Source audit only; no Lean compilation, no inequality.

## 1. What the 2.5 coefficient actually is

tmp/sheaf/xif/paper/PaperWeightedThetaSignedActual.lean computes, for
l = 5 and one bad place b,

  (1/|F_5^x|) * sum_{j in F_5^x} log( q_v^{j^2} )
    = (1/4) * (1^2 + 2^2 + 3^2 + 4^2) * log(q_v)
    = (10/4) * log(q_v)
    = (5/2) * log(q_v).

Since q_v < 1, this is negative, and with the q_v log-magnitude
baseQLogMagnitude = -log(q_v), it is

  -(5/2) * baseQLogMagnitude.

The weighted global scalar is then

  sum_b nativeBadLocalWeight(b) * (-(5/2) * baseQLogMagnitude(b))
    = -(5/2) * nativeGlobalQPilotNormalizedLogMagnitude.

So the 2.5 comes from averaging the theta logarithms over F_l^x first,
then applying the V_bad weights. It is the logarithm of the geometric mean of
the theta values, not a log-volume of a holomorphic hull.

## 2. What the paper actually defines

IUT III, Theorem B, pp. 21-22 (extraction lines 1198-1229) and Corollary 3.12,
pp. 173-174 (lines 10499-10535):

  -|log(Theta)|

is the procession-normalized mono-analytic log-volume of the holomorphic
hull of the union of the possible images of the Theta-pilot object, relative
to the Kummer isomorphisms, subject to (Ind1), (Ind2), (Ind3).

The order in the source is:

1. for each procession label j, form the union of possible images (over the
   relevant places/indeterminacies);
2. form the holomorphic hull of that union;
3. take the actual log-volume of the hull;
4. only then take the procession average over j in F_l^x.

In symbols, the paper's quantity has the shape

  average_{j in F_l^x}
    ( - logVol( hull( union of possible images at j ) ) ),

not

  - logVol( hull( union_j ( theta value at j ) ) )

and certainly not

  average_j ( log theta value at j ).

The first object uses a nonlinear hull operation before averaging; the last
object averages ordinary logarithms and has no hull at all.

## 3. Why equality is not available

The 2.5 object and the paper quantity differ in two independent ways:

1. Order of operations. The hull operation is nonlinear. In general,
   logVol(hull(U)) is not the average of logVol(U_j), and the hull of a union is
   not the union of the hulls. Averaging theta logs first cannot be rewritten as
   a hull log-volume.
2. Theta values are not hull volumes. The source theta values
   q_v^{j^2} are local monoid generators up to torsion (IUT III, Definition
   3.8, (i), lines 6731-6769), not the log-volumes of the possible-image hulls.
   The hulls are formed after transporting possible images through the
   multiradial/Kummer data and imposing (Ind1)-(Ind3).

Therefore the 2.5 coefficient is an average-first theta-log coefficient.
It is not the paper's -|log Theta| and must not be used as that quantity.

## 4. Consistency check: the direction already shows the mismatch

For l = 5, the paper's Corollary 3.12 says

  -|log Theta| >= -|log q|,

equivalently |log Theta| <= |log q|.

The average-first object has signed value -(5/2) Q, while the q-pilot signed
value is -Q. Thus the average-first object gives

  -(5/2) Q < -Q   (for Q > 0),

i.e. the opposite direction. This is not a counterexample to the paper; it
shows that the 2.5 object has the wrong magnitude because it is the wrong
operation order. The paper quantity must be built from the actual hull
log-volume and then averaged.

## 5. Correction object required

The corrected object must be a hull-then-average object:

* an actual possible-image set for each F_l^x procession label;
* an actual holomorphic hull of that possible-image set;
* an actual Haar/mono-analytic log-volume of each hull;
* a final procession average over F_l^x of those hull log-volumes.

The average-first scalar weightedThetaSignedScalar remains a legitimate
actual scalar, but its correct name is an averaged theta-log scalar, not the
paper's -|log Theta|. No equality between it and the paper quantity is
asserted. No inequality is asserted here; the direction comparison above is
only a consistency check on the wrong object.

## 6. References

- IUT III, Definition 3.8, (i), p. 112: extraction lines 6731-6769.
- IUT III, Theorem B, pp. 21-22: extraction lines 1198-1229.
- IUT III, Corollary 3.12, pp. 173-174: extraction lines 10499-10535.
- IUT II, pp. 2-3: extraction lines 99-108 (theta values q_v^{j^2}).
- Project average-first object:
  tmp/sheaf/xif/paper/PaperWeightedThetaSignedActual.lean,
  weightedThetaSignedScalar, weightedThetaCoefficient_five.
