# S1966: local theta / Gaussian monoid, and the exact first missing

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S1966LocalThetaMonoidActual.lean.

## Outcome

**Constructed (monoid level) + missing for the paper-level assignment.**  The
file constructs, kernel-checked, the Gaussian ray, the formal log direction
and its evaluation, the finite theta-packet Gaussian value monoid, and the
actual-local semi-simplified theta/Gaussian monoid.  It does **not** claim to
construct the paper's full local theta monoid

  PsiFenv(daggerHT_Theta) = { Psi_{daggerF_Theta,v} }_{v in V}

of IUT II, Corollary 4.6, (iv).  The exact first missing is Psi_cns(Pi_v), the
group-theoretic constant monoid of IUT II, Proposition 4.1, (i).  No fake
monoid, empty type, arbitrary inhabitant, sorry or axiom is used.

## Constructed (checked, EXIT=0)

### 1. The Gaussian ray of Proposition 4.1, (iv)

For a prime p and a prime-at-least-five label l:

* ThetaLabel l = Fin (lStar l.value) is the paper's index j = 1, ..., l^*;
* gaussianWeight p l j = (j+1)^2 * log p (the paper's j^2 log(p_v));
* gaussianRay p l is the actual submonoid

    { c * (j |-> (j+1)^2 * log p) | c : R>=0 }

  of (ThetaLabel l -> R), with gaussianRayHom p l : R>=0 ->+ gaussianRay p l
  and gaussianRayHom_bijective (an additive bijection);
* thetaRay = R>=0 is the formal coefficient monoid
  R>=0 * log(p_v) * log(Theta) (the formal symbol is the generator 1), and
  thetaToGaussian p l is the formal evaluation
  c |-> c * (j |-> (j+1)^2 * log p); thetaToGaussian_bijective proves it is
  bijective onto the Gaussian ray.  This is exactly the non-unit part of the
  evaluation of Proposition 4.1, (iv).

### 2. The finite theta-packet Gaussian value monoid

For every packet : FiniteThetaPacket l:

* packetProfile packet : ThetaLabel l -> R is xi j = packet.scale (j+1);
  packetProfile_thetaZero gives q and packetProfile_thetaOne gives q^4;
* packetGaussianValueMonoid packet is the genuine submonoid
  (R^x)<F_l^*> * xi^N of (ThetaLabel l -> R), i.e. diagonal real units times
  the N-th powers of the value profile (Corollary 3.5, (ii)/3.6, (ii));
* packetEvaluation packet : R^x x N ->* packetGaussianValueMonoid packet is
  (u,n) |-> diag(u) * xi^n; it is bijective when packet.q != 1
  (packetEvaluation_bijective).  packetEvaluation_generator sends the formal
  generator to xi and packetEvaluation_units is the identity on units;
* gaussianFivePacket l is the packet q = 1/5; C3GaussianThetaPacketActual
  identifies the source theater's packet with FiniteThetaPacket.ofQ (1/5).
  gaussianFivePacket_evaluation_injective is the checked q = 1/5 instance.

This is the requested "at least finite theta packet -> monoid" construction.
It is a real-valued finite model; it is not the paper's nonarchimedean
Psi_gau.

### 3. The actual-local semi-simplified theta/Gaussian monoid

For v : FinitePrimePlace 2 7, using the actual local units

  ActualLocalUnits v = (IndIntegralMonoid (finitePrimePlaceToQ v))^x

(the ind-topological integral monoid of IUT I, Definition 5.2, (v),
reconstructed in Iut/Foundations/SourceDefinition52LocalReconstruction.lean):

* LocalSemiSimplified v = ActualLocalUnits v x Multiplicative R>=0 is the
  paper's Psi_ss = Psi_cns^x x R>=0 on the actual-local-field model;
* LocalThetaMonoidModel v is the same carrier, representing units times the
  formal R>=0 * log(p_v) * log(Theta) direction;
* localGaussianValueMonoid v p l is the submonoid

    units<F_l^*> * { c * (..., j^2 log(p_v), ...) }

  of (ThetaLabel l -> LocalSemiSimplified v);
* localEvaluation v p l : LocalThetaMonoidModel v ->* localGaussianValueMonoid v p l
  is (u,c) |-> diag(u) * c * (..., j^2 log p, ...); it is bijective
  (localEvaluation_bijective).  localEvaluation_units is the identity on
  units, and localEvaluation_generator sends the formal generator to the
  Gaussian vector.

This is a genuine local theta/Gaussian monoid on the actual local-field model,
not a carrier record and not an arbitrary one-point monoid.  It is named
...Model because it uses the actual local units as a model of Psi_cns^x; the
identification with the paper's Psi_cns(Pi_v) is the missing step (below).

### 4. Consumer

Every Hodge theater's finite packet yields the monoid
hodgePacketGaussianValueMonoid HT = packetGaussianValueMonoid HT.thetaPacket,
with hodgePacketGaussianValueMonoid_thetaZero proving its value at label 1 is
HT.thetaPacket.q.  This is the consumer inside the tree's HodgeTheater layer.

## Exact first missing

The paper's Psi_cns(Pi_v) is constructed by the group-theoretic algorithm of
[AbsTopIII], Corollary 1.10, (b), from the topological group Pi_v; it is an
ind-topological submonoid of lim H^1(J, mu_hat^Z(G_v)), isomorphic to O^tri_{F_v}
(IUT II, Proposition 4.1, (i)).  The first missing object is this Psi_cns(Pi_v)
together with its G_v(Pi_v)-action.

Evidence and precise boundaries:

1. **No group-theoretic Psi_cns.**  The active tree has no construction of
   Psi_cns(Pi_v) from Pi_v by the algorithm of [AbsTopIII], Corollary 1.10, (b),
   and no G_v(Pi_v)-action on such a monoid.  There is no H^1(J, mu_hat^Z(G_v))
   constant-monoid construction in LeanFormal/Iut.
2. **Actual local-field models exist but are not Psi_cns.**  The tree has
   IndIntegralMonoid (Iut/Foundations/SourceDefinition52LocalReconstruction.lean),
   with its ind-topology and Krull action, and SourceLogShellDatum.Units
   (LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean).  These are actual
   local-field models of O^tri; the file uses the former for ActualLocalUnits.
   No identification of these models with Psi_cns(Pi_v) or its units is
   constructed.  The group action used here is the Krull action on the actual
   local field, not G_v(Pi_v) reconstructed from Pi_v.
3. **No R>=0(Pi_v).**  The paper's R>=0(Pi_v) and its distinguished element
   log(p_v) are constructed by the group-theoretic algorithm of Proposition
   4.1, (ii).  The file represents log(p_v) by the real number Real.log p and
   the coefficient ray by Multiplicative R>=0, but does not construct the
   paper's R>=0(Pi_v).
4. **No full Psi_env / Psi_gau.**  Because Psi_cns(Pi_v)^x, the diagonal
   <F_l^*> units, and the G_v(Pi_v)-actions/splittings of Proposition 4.1,
   (iii)--(iv), are missing, the paper's Psi_env(Pi_v) and Psi_gau(Pi_v) are
   not defined.  The file's LocalThetaMonoidModel/localGaussianValueMonoid are
   explicitly models on the actual local units, not the paper's objects.
5. **Bad v: no Theta_v / theta monoid.**  At bad v the local construction is
   the Frobenioid-theoretic theta monoid of IUT II, Corollary 3.6, (ii), built
   from the theta function Theta_v in O^x(T^div).  The tree has only the finite
   real theta packet (FiniteThetaPacket, q^j^2), not Theta_v as an element of a
   Frobenioid theta monoid; this is the exact first missing on the bad-place
   branch.  SourceThetaLinkDivisorMonoidDisplacementReduction already records
   that the finite Gaussian evaluation stands in for the theta comparison and
   that the bridge to the local divisor monoid is missing (card C2b-general).
6. **No assignment / gluing.**  The assignment over all v and the Theta-bridge
   gluing of Corollary 4.6, (iv), are not constructed; the HodgeTheater layer
   records only a finite thetaPacket and an arbitrary primeStrip.
7. **Existing finite LGP monoid is not this object.**  SourceLGPMonoidLayer
   defines a finite LGP splitting monoid generated by real theta values at
   q = 2; its own documentation says it is not the paper's global Gaussian U_j.
   It is not identified with any monoid in this file.

Consequently the paper-level first object PsiFenv is **missing**; the file's
constructions are genuine partial results at the monoid level, with the exact
gap being the group-theoretic constant monoid Psi_cns and its action.

## Evidence

* source SHA256:
  B152CB535322E394F2A38138544F8F5257B948B33C701E4B5153DDD2D3B64CA5
* EXIT=0:
  lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1966LocalThetaMonoidActual.olean tmp/sheaf/xif/paper/S1966LocalThetaMonoidActual.lean
* olean: 800480 bytes, SHA256
  064C530A05D91CB9CCCDBB986D842AADD22E99CB51CC90FFB255A08D4567F73C
* axioms: propext, Classical.choice, Quot.sound only; no sorryAx, no custom
  axiom.  The file ends with #print axioms for thetaToGaussian_bijective,
  packetEvaluation_injective and localEvaluation_injective.
* consumer: tmp/sheaf/xif/paper/_S1966Consumer.lean, EXIT=0; it checks
  thetaToGaussian_bijective, packetEvaluation_bijective,
  gaussianFivePacket_evaluation_injective, localEvaluation_bijective,
  localEvaluation_generator, localEvaluation_units and the HodgeTheater
  consumer.

## Not run

Full Project build, target comparator, independent review.

## Next executable step

Construct Psi_cns(Pi_v) from Pi_v with its G_v(Pi_v)-action (Proposition
4.1, (i)), or prove that the actual IndIntegralMonoid model is isomorphic to it
as a G_v(Pi_v)-monoid.  Then form Psi_env and Psi_gau with the diagonal
<F_l^*> units and the splittings of Proposition 4.1, (iii)--(iv); the present
file supplies the exact Gaussian ray and the evaluated monoid into which they
map.  At bad v, the next missing object is the Frobenioid-theoretic theta
function Theta_v / theta monoid of Corollary 3.6, (ii).
