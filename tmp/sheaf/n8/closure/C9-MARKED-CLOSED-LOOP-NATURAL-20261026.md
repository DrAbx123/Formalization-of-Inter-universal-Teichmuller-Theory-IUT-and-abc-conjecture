# C1 marked closed-loop: natural-language source proof

Date: 2026-10-26. Owner: root, single agent. Stage: SHEAF stage 1.
Status: the scalar gate closes only under the stated xi-e/xi-f source
assertion; the independent fixed-q source construction remains open. The
paper-carrier/determinant compatibility subproblem is closed at source level.

This note records one concrete route through the hull-carrier compatibility
gate. It does not redefine the output family, add a q-membership field, or use
the Input-boundary A1/A2/A3 proof as a premise. The output family below is the
one produced by the paper's multiradial algorithm, with its stated formal
indeterminacies.

## 1. The marked state

Fix one paper-admissible initial data set `C`, including the q-pilot at `(1,0)`,
the Theta-times-mu LGP link, the procession, the original weights, the common
tensor power `M`, the `O(-)` reference, and the signed normalization.

At every stage of the construction keep a triple

```text
(X, mark, carrier)
```

where `X` is the current `F^(boxplus-triangleright-times-mu)` prime-strip,
`mark` is the transported q-intertwining of the fixed q-pilot, and `carrier`
is the arithmetic object on which the current operation is expressed. The
mark is not a numerical equality and is not a choice of an arbitrary point in
the hull. It is the source prime-strip morphism/structure poly-morphism that
is transported by the construction.

The initial state is the q-pilot prime-strip with its native q-intertwining and
readout `Q_C`. The desired conclusion is that a final marked state has a
signed readout at least `Q_C` up to the source's allowed approximation.

## 2. Mark preservation through the five operations

The operations are those named in the proof of Corollary 3.12, xi-b--xi-e.
The following is a source-level transport argument, not a new interface
assumption.

1. **sQ1 and sQ2.** Kummer detachment and Galois evaluation are the first
   arrows in the Remark 3.10.2 square. The IPL factorization is the composite
   of the inverses of the two lower horizontal arrows, the first vertical
   Kummer arrow, and the upper evaluation arrows. Therefore the q mark is
   carried to the output prime-strip by an actual full-strip
   poly-isomorphism. No scalar readout is taken yet.

2. **sQ3.** Passing to a holomorphic hull and to a positive tensor power of
   its determinant changes the carrier from a region to a rank-one arithmetic
   object. cQ3 puts these hull determinants, their structure poly-morphisms,
   and their local/global localizations into the stated formal-quotient
   category of compatible collections. cQ3 by itself does not say that an
   arbitrary local collection has a global q-map. The extra fact used here is
   the closed-loop assertion: the chain beginning with the q-pilot strip
   actually passes through sQ3 and sQ4, and those operations are compatible
   with the q strip data. Thus the mark is retained by this particular source
   chain, not created from mere nonemptiness of the cQ3 category. This is where
   the common `M` and the original `O(-)` reference are fixed; a Haar or
   determinant normalization cannot be selected after the fact.

3. **sQ4.** The vertical shift adjustment is made by the log-Kummer
   correspondence. cQ4 says that this adjustment is compatible with the
   local Galois and etale/Frobenius-like unit data, modulo the explicitly
   allowed iterates of the log-link. Hence the mark remains a mark of the
   same prime-strip object after the shift. It is not replaced by an arbitrary
   scalar rescaling.

4. **sQ5.** Only after the marked determinant object exists do we forget the
   local structure and take its procession-normalized signed log-volume.
   Ind1 and Ind2 leave this readout invariant; Ind3 gives the stated
   one-sided inequality. The output readout is therefore the image of a
   marked state, rather than a number reconstructed from the desired answer.

The closed-loop assertion of Remark 3.9.5(ix) is precisely what makes the
composite of these transports a valid marked state. A non-closed loop would
not retain the simultaneous q- and Theta-intertwining and would yield no
nontrivial scalar consequence. This is a groupoid/stack-style transport
argument: it transports a marked object through compatible local-global
collections and quotients by the stated indeterminacies. It does not require
choosing unrelated local maps and proving that they descend to one strict
global linear map. Such a strict map is one possible formalization route, not
the source theorem's only route.

## 3. The marked readout lemma

Let `R_C^mark` be the set of signed readouts of final-evaluation states that
are obtained by the preceding marked operations, including the paper's
Ind1--Ind3 and formal-quotient representatives. Let `h_C` be the signed
log-volume of the canonical holomorphic hull, with the same determinant,
reference, tensor power, procession weights, and normalization.

The construction gives the following two facts.

```text
(H)  every r in R_C^mark satisfies r <= h_C;

(M)  either Q_C belongs to R_C^mark, or, for every epsilon > 0, there is
     r_epsilon in R_C^mark with Q_C - epsilon <= r_epsilon.
```

`(H)` is hull minimality plus signed Haar monotonicity after the sQ3/sQ4
normalization. It is the object-level carrier result proved in the preceding
carrier records. `(M)` has two readings that must not be conflated. The
literal scalar conclusion of xi-f is exact: it says that the input q-pilot
log-volume belongs to the ray of possible output log-volumes bounded by `h_C`.
The parenthetical “perhaps only up to some sort of approximation” concerns how
the output construction realizes the pilot under indeterminacies; it does not
provide a quantified epsilon statement in the text. Therefore an exact
membership Lean target may follow the literal xi-f reading, while an epsilon
target must first make the approximation relation precise from the source and
prove its quantifiers. Under the exact output reading, `(M)` is `exists r, r
in R_C^mark and r = Q_C`.

This formulation is deliberately weaker than demanding that every local
collection have zero divisor defect. A source comparison may instead produce
`h_C - Q_C = S_C - kappa_C`; it is enough to prove `S_C >= kappa_C`, or to
produce the marked epsilon family in `(M)`. The condition `kappa_C = 0` is a
sufficient special case, not part of the gate definition.

## 4. Scalar conclusion

If the source gives the quantified approximation branch of `(M)`, and
`Q_C > h_C`, choose `epsilon = (Q_C - h_C)/2`. Then `(M)` gives a genuine
marked output with

```text
Q_C - epsilon <= r_epsilon <= h_C < Q_C - epsilon,
```

which is impossible. Thus `Q_C <= h_C`. Under the literal exact-membership
reading of xi-f, the proof is even shorter: choose the marked output whose
readout is `Q_C` and apply `(H)`. This direct source reading is the one used
for the paper-level conclusion; the epsilon proof applies only after a
quantified approximation has been established.

No output is defined by setting its readout equal to `Q_C`; its membership is
obtained from the marked closed loop and the source xi-e/xi-f construction.

## 5. What this settles about C1 and A1/A2/A3

There are two different dependency questions.

* At the **reduced Lean interface**, A1/A2/A3 do not imply `(M)`. The existing
  singleton/identifiability model proves that an output membership field can
  hold while exact q-readout fails. Therefore C1 is logically independent of
  the abstract A1/A2/A3 records.
* At the **paper source level**, `(M)` is not an additional arbitrary axiom:
  it is the readout assertion made in xi-e/xi-f after the marked closed loop
  has been constructed. Under that source reading, the natural-language C1
  gate is closed by the proof above. A1/A2/A3 need not be proved first; they
  provide the output, log-volume, and hull interfaces used by the same source
  construction and can be formalized in parallel.

Thus the correct order is:

```text
source marked closed loop (xi-e/xi-f)
  -> marked q readout (exact or epsilon)
  -> hull monotonicity
  -> Q_C <= h_C
  -> A1/A2/A3 and the Corollary 3.12 bridge consume the result.
```

The Input-boundary A1/A2/A3 Lean proof is already kernel-closed and is not a
prerequisite for this source-level route. Conversely, a Lean proof that starts
from A1/A2/A3 but omits the marked q-readout construction would still leave
C1 open.

## 6. Formalization boundary

The paper proof above is complete under the source assertions of Theorem 3.11,
Remark 3.9.5(ix), and xi-e/xi-f. It is not an independent derivation of xi-f
from the abstract A1/A2/A3 interfaces. To formalize the source route in Lean,
the repository must construct, rather than postulate, the following data for
the actual source input:

```text
q-marked prime-strip
  -> compatible sQ3 hull/determinant local-global collection
  -> cQ4 log-Kummer-compatible shift
  -> closed-loop/Ind quotient relation to a Theorem 3.11 output
  -> original M/reference/weight-normalized readout.
```

The current reduced `SourceKummerEvaluationArrows` and
`SourceArithmeticHolomorphicLanding` records do not contain this marked
source construction; their identity/zero-bundle witnesses are not valid
substitutes. Therefore the natural-language gate is closed at paper level,
while the independent Lean node remains `stage1=open`,
`proof_status=open`, and `target_accepted=false` until this source data is
actually built.

The natural next Lean object is a groupoid/stack or relation of marked
prime-strip realizations with the actual local-global collection morphisms,
and functors/relations for sQ1--sQ5. Prove that the actual closed-loop composite
preserves the q mark before applying the real-valued log-volume functor. A
strict global linear-map square can be one implementation if the source
constructs it, but requiring it up front could strengthen the paper claim.

Sources checked: IUT III `sources/IUT-III.txt`, lines 8264--8358 (cQ3/cQ4),
8390--8416 (closed loop), 10570--10715 (xi-a--xi-f), and 10977--11022
(fitw logical form); existing carrier and marked-image records dated
2026-10-24--26.
