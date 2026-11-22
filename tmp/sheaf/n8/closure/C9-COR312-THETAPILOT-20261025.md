# C9 Corollary 3.12: Theta-pilot/procession log-volume definitions

Task: task-378. Owner: qside. Date: 2026-10-25.
Exact source extraction from IUT III; no black-box citation; no mixed/E3;
no Lean/Project edits; only this file written.

Source: tmp/sheaf/n8/closure/sources/IUT-III.txt
SHA256: 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D
(566015 bytes, 11456 lines).

Primary locations:
- Definition 3.8, (i): lines 6506-6544.
- Proposition 3.9: lines 6724-6815.
- Remark 3.9.5: lines 7527-7626; determinant (Ob3): lines 7770-7868.
- Theorem 3.11: lines 8999-9460; Ind1/Ind2: 9105-9119; Ind3: 9282-9294.
- Corollary 3.12: lines 10152-10180; possible-image sets: 10202-10233.
- Proof (x)-(xi): lines 10520-10780; A1/A2/A3: xi-a to xi-f, 10571-10715.

## 0. Verdict

IUT III gives a precise schema, not an explicit construction of a complete C:

A1. q-pilot input: a q-pilot object at (1,0), with fixed
    procession-normalized log-volume -|log(q)| in R; not subject to
    Ind1/Ind2/Ind3.
A2. determinant/log-volume comparison: the multiradial algorithm
    (Theorem 3.11), followed by holomorphic hull and det^{tensor M},
    produces comparable regions R_{<= -|log(Theta)|} and -|log(q)| in R.
A3. fixed q-pilot value: because the q-pilot log-volume is a possible output
    of the algorithm, -|log(q)| belongs to R_{<= -|log(Theta)|}; hence
    -|log(q)| <= -|log(Theta)| (Corollary 3.12).

The proof is a tautological construction-computation (Step (xi)), not an
explicit C construction. It does not construct explicit archimedean r_v,
B_I membership, or a complete C.

## 1. Theta-pilot and q-pilot objects (Definition 3.8)

Definition 3.8, (i) (lines 6506-6544):

- The Theta-pilot object is the object of
    prod_{j in F_l^x} (dagger F^circledast_MOD)_j
  or
    prod_{j in F_l^x} (dagger F^circledast_mod)_j,
  as well as its realification, regarded as an object of
    dagger C^Vdash_LGP = C^Vdash_LGP(dagger HT^{Theta±ellNF})
  or
    dagger C^Vdash_lgp = C^Vdash_lgp(dagger HT^{Theta±ellNF}),
  determined by any collection, indexed by v in V_bad, of generators up to
  torsion of the monoids
    Psi_perp_{F_lgp}(dagger HT^{Theta±ellNF})_v.
- The q-pilot object is the object of the global realified Frobenioid
    dagger C^Vdash_Delta
  determined by any collection, indexed by v in V_bad, of generators up to
  torsion of the splitting monoid associated to the split Frobenioid
    dagger F^dashv_{Delta,v}
  — concretely, by the q_v, for v in V_bad.

Exact consequences:
(D1) A pilot object is not a single point. It is an object determined by a
     collection of generators up to torsion. Possible images are images of
     this object, not elements of a canonical set.
(D2) The Theta-pilot object lives in F^circledast_MOD (multiplicative) or
     F^circledast_mod (additive/integral); the q-pilot object arises from the
     split Frobenioid and q_v. They are related by the Theta-times-mu LGP-link
     (Definition 3.8, (ii)).

## 2. Procession-normalized mono-analytic log-volume (Proposition 3.9)

### 2.1 Packet normalization

Proposition 3.9, (i) (lines 6724-6778):

- Nonarchimedean v: p_{v_Q}-adic log-volume on each direct summand field is
  normalized so that
      log-volume(local holomorphic integral structure O) = 0,
      multiplication by p_v adds -log(p_v) in R.
  This is the packet-normalization.
- Archimedean v: the sum of radial log-volumes on the direct summand complex
  fields is normalized so that
      log-volume(product integral structure O) = 0,
      multiplication by e=2.71828... adds 1=log(e) in R.
  This is also the packet-normalization.

### 2.2 Procession normalization

Proposition 3.9, (i) (lines 6773-6778):

For a collection of capsules in a procession, take the average of the
packet-normalized log-volumes over the capsules. This is the
procession-normalization.

Proposition 3.9, (ii) (lines 6779-6815) transports it to mono-analytic
log-shells: p_{v_Q}-adic log-volume for nonarchimedean v_Q, radial log-volume
for archimedean v_Q, adjusted for the discrepancy between local holomorphic and
mono-analytic integral structures. The resulting log-volumes are compatible
with the natural poly-isomorphisms of Proposition 3.2, (i). Averaging the
packet-normalized log-volumes of a mono-analyticized holomorphic procession
gives the procession-normalized log-volumes; replacing D^dashv by F^{dashv x mu}
gives the analogous theory for log-shells I dagger F^{dashv x mu}_v.

### 2.3 Global log-volume

Proposition 3.9, (iii) (lines 6816-6849):

For a global collection with all but finitely many components of zero
log-volume, summing over v_Q gives the global log-volume. It is invariant under
multiplication by elements of the M^circledast and under permutations of A,
and equals the degree of the associated arithmetic line bundle. This is the
comparison bridge to the q-pilot.

## 3. Holomorphic hull (Remark 3.9.5, (i))

Remark 3.9.5, (i) (lines 7527-7554):

Let U subset IQ(F_{v_Q}) (or IQ(AF_{v_Q}), or IQ(A,alpha F_v)) contain a
relatively compact subset of finite log-volume (> -infinity).

- If U is relatively compact, the holomorphic hull of U is the smallest subset
  of the form
      H = lambda · O_{F_{v_Q}}
  (respectively lambda·O_{AF}, lambda·O_{A,alpha F}) that contains U, where
  lambda is an element each of whose direct-sum components is nonzero.
- If U is not relatively compact, the holomorphic hull of U is the whole
  IQ(F_{v_Q}).

Remark 3.9.5, (ii) (lines 7555-7583): the hull is a canonical map
phi: P -> H from direct-product regions to hulls characterized by:
(P1) phi(H)=H for H in H;
(P2) P subset phi(P);
(P3) P1 subset P2 implies phi(P1) subset phi(P2);
phi(P) = intersection of all H containing P.

This is a minimal enclosing region, not a set of possible points. If the
union is not relatively compact, its hull is the full IQ and its log-volume
may be +infinity.

## 4. Possible images and indeterminacies Ind1/Ind2/Ind3

### 4.1 Possible images

Corollary 3.12 (lines 10152-10242):

-|log(Theta)| in R union {+infinity} is the procession-normalized mono-analytic
log-volume (average over j in F_l^x; Remark 3.1.1(ii)-(iv); Proposition
3.9(i)-(ii); Theorem 3.11(i)(a)) of the holomorphic hull (Remark 3.9.5(i)) of
the union of the possible images of a Theta-pilot object (Definition 3.8(i)),
relative to the relevant Kummer isomorphisms (Theorem 3.11(ii)), in the
multiradial representation of Theorem 3.11(i), subject to (Ind1),(Ind2),(Ind3).

Proof (lines 10202-10233): for j in |F_l| and v_Q in V_Q,
  n,circ U_{j,v_Q} subset n,circ U^Q_{j,v_Q}
      = IQ(S^±_{j+1}; n,circ D^dashv_{v_Q})
      [Theorem 3.11(i)(a)];
  n,circ U_{j,v_Q} = union of possible images of a Theta-pilot object relative
      to Kummer isomorphisms in the multiradial representation, subject to
      Ind1/2/3;
  n,circ U = { n,circ U_{j,v_Q} } subset n,circ U^Q;
  n,circ U_{j,v_Q} = holomorphic hull of n,circ U_{j,v_Q}.
The union is over labels j and places v_Q.

### 4.2 Ind1

Theorem 3.11(i) (lines 9105-9108):

(Ind1) the indeterminacies induced by the automorphisms of the procession of
D^dashv-prime-strips
    Prc(n,circ D^dashv_T)
that gives rise to the tensor packets of (a).

### 4.3 Ind2

Theorem 3.11(i) (lines 9108-9119):

(Ind2) for each v_Q in V^non_Q (respectively V^arc_Q), the indeterminacies
induced by the action of independent copies of Ism on each direct summand of
the j+1 factors in the tensor product defining
IQ(S^±_{j+1}; n,circ D^dashv_{v_Q}); for archimedean v_Q, copies of each of the
order-2 automorphisms whose orbit constitutes the poly-automorphism of
Proposition 1.2(vii).

### 4.4 Ind3

Theorem 3.11(ii) (lines 9282-9294):

(Ind3) as m in Z varies, the isomorphisms of (a) are upper semi-compatible,
relative to the log-links of the n-th column of the LGP-Gaussian
log-theta-lattice, in a sense involving:
    natural inclusions "subset" at v_Q in V^non_Q, and
    natural surjections "onto" at v_Q in V^arc_Q.
The isomorphisms of (a) are precisely compatible, as m varies, with the
respective log-volumes (Proposition 3.9(iv)).

Ind3 is not a finite group action; it is an upper semi-compatibility
(inclusion/surjection) relation. From lines 10542-10550: procession-normalized
mono-analytic log-volumes in R are invariant under (Ind1),(Ind2), and convert
(Ind3) into an inequality from above.

## 5. Exact Corollary 3.12 statement

Corollary 3.12 (lines 10152-10180):

Let -|log(Theta)| in R union {+infinity} be as in 4.1, and let -|log(q)| in R
be the procession-normalized mono-analytic log-volume of the image of a q-pilot
object (Definition 3.8(i)), relative to the relevant Kummer isomorphisms
(Theorem 3.11(ii)), in the multiradial representation of Theorem 3.11(i), NOT
regarded as subject to Ind1/2/3.

Here |log(q)|>0 is computed from the q-parameters of E_F at v in V_bad
(nonempty). Then:
    -|log(Theta)| in R,
    -|log(Theta)| >= -|log(q)|,
i.e. C_Theta >= -1 for any real C_Theta such that
    -|log(Theta)| <= C_Theta · |log(q)|.

Exact signs: |log(q)|>0, so -|log(q)| is negative. The notation -|log(Theta)| is
chosen to express that it is a positive real multiple of -|log(q)| plus a
possible error (a priori +infinity). The theorem proves finiteness and the
displayed inequality.

## 6. A1-A3 source schema

A1 q-pilot input/representation. Definition 3.8(i); Cor3.12; Step (xi-a),(xi-e)
(lines 10571-10581, 10682-10711):
- q-pilot object at (1,0) determined by q_v at v in V_bad;
- represented via F^circledast_mod and the log-Kummer correspondence in the
  1-column on the mono-analytic container 1,circ U^Q;
- log-volume fixed -|log(q)| in R, |log(q)|>0; not subject to Ind1/2/3;
- Theta-times-mu LGP-link from (0,0) to (1,0) identifies the Theta-pilot object
  at (0,0) with the q-pilot object at (1,0).

A2 determinant/log-volume comparison. Theorem 3.11(i)(a); Step (xi-b)-(xi-d)
(lines 10582-10681); Remark 3.9.5(vii),(Ob3),(Ob4) (lines 7770-7868):
- algorithm yields possible output data in 1,circ U subset 1,circ U^Q satisfying
  IPL and SHE, linked by F^Vdash-prime-strip isomorphisms to the q-pilot
  representation on 1,circ U^Q;
- holomorphic hull expresses output data via localizations of arithmetic vector
  bundles over local rings of the 1-column; localizations rank>1;
- compare with q-pilot line bundle via det^{tensor M} (weighted tensor powers,
  inverse structure-sheaf determinant normalization; arithmetic degree =
  log-volume);
- apply normalized log-volume to 1,circ U and the q-pilot region, obtaining
      R_{<= -|log(Theta)|} = {lambda in R | lambda <= -|log(Theta)|},
      -|log(q)| in R.

A3 fixed q-pilot value and inclusion. Step (xi-e)-(xi-f) (lines 10682-10715):
- -|log(q)| is the fixed pilot log-volume prescribed by the 1-column
  arithmetic holomorphic structure;
- SHE expressibility is under the condition that the input pilot log-volume
  equal this fixed value;
- hence the construction of R_{<= -|log(Theta)|} constructs the input
  q-pilot log-volume; so -|log(q)| in R_{<= -|log(Theta)|};
- therefore -|log(q)| <= -|log(Theta)| in R and C_Theta >= -1.

## 7. Proved vs. exact gaps

PROVED/EXTRACTED:
- Definition 3.8 roles of Theta-pilot/q-pilot (generators up to torsion, not
  canonical points).
- Proposition 3.9 packet/procession normalization and global log-volume.
- Remark 3.9.5 holomorphic hull minimal region/full IQ.
- Theorem 3.11 Ind1/Ind2/Ind3 exact descriptions.
- Cor3.12 definitions and inequality.
- Step (xi) A1-A3 schema and determinant comparison.

GAPS:
(G1) The construction depends on the full Theorem 3.11 multiradial algorithm,
     log-Kummer correspondence, Kummer-detachment, and IPL/SHE/APT. This
     extraction verifies the schema from source, not an independent construction
     of these algorithms.
(G2) Theta-pilot object is determined by a collection of generators up to
     torsion; the union of possible images is over j and v_Q and is subject to
     Ind1/2/3. There is no canonical single possible-image set.
(G3) Ind3 is upper semi-compatibility (inclusions nonarchimedean, surjections
     archimedean), not finite group action. Procession-normalized log-volume is
     invariant under Ind1/Ind2 and converts Ind3 into an inequality from above;
     IUT III gives no quantitative Ind3 error (IUT IV gives explicit estimates).
(G4) The hull can be the whole IQ (hence +infinity) if the union is not
     relatively compact. Cor3.12 handles finiteness by compactness of
     1,circ U_{j,v_Q}; no explicit archimedean r_v or B_I membership.
(G5) |log(q)|>0 is asserted to be easily computed from q-parameters; IUT III
     does not give the explicit numerical formula.
(G6) No explicit complete C in IUT III. The theorem is universal over the
     initial Theta-data/situation of Theorem 3.11; P6-true does not require an
     explicit C, but source hypotheses must be supplied.
(G7) -|log(q)| is not a point of the Theta hull; it is a log-volume of the
     q-pilot region linked to possible output data. The inclusion is at the
     level of possible pilot-object log-volumes.

No B_I-as-hull, no h_inf lower bound, no explicit C, no mixed/E3 claim.

## 8. Conclusion

Cor3.12 is a source theorem with schema:
  A1 q-pilot input/representation
  -> A2 determinant/procession-normalized log-volume comparison
  -> A3 fixed q-pilot value is a possible output
  -> -|log(q)| <= -|log(Theta)|, C_Theta >= -1.

The definitions of Theta-pilot object, possible images, holomorphic hull, and
procession-normalized mono-analytic log-volume are extracted above with exact
source locations. The construction-computation is tautological and universal;
it does not construct explicit complete C or explicit archimedean r_v. Exact
gaps are G1-G7.

target_accepted=false.

## 9. Source locations

- IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.
- Definition 3.8: 6506-6544.
- Proposition 3.9: 6724-6815.
- Remark 3.9.5: 7527-7626; Ob3: 7770-7868.
- Theorem 3.11: 8999-9460; Ind1/Ind2 9105-9119; Ind3 9282-9294.
- Cor3.12: 10152-10180; possible images 10202-10233.
- Proof Steps (x)-(xi): 10520-10780; A1/A2/A3 10571-10715.
