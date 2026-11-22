# C9 new source theorem attempt: global height positivity via a theta divisor

Task: task-253 (C9-NEW-HEIGHT-POSITIVE-20261025). Owner: logdescent. Date: 2026-10-25. New-math source-theorem program; natural-language construction/proof attempt; only this file written; no Lean/Project/target/other-owner edits; no arbitrary assumptions. P6 unproved; target_accepted=false.

Inputs: C9-GLOBAL-ASSEMBLY (corrected), C9-UNIFORM-HULL, C9-NEW-VARIATIONAL-COUNTEREXAMPLE (task-245), C9-ARCH-HULL (task-240), C9-ARCH-NORMALIZATION-CORRECTION, E_j/alternative-E files, IUT III/IV.

## 0. Verdict

A genuine source-level global height theorem identifying Q_C-h_C with the Arakelov degree of a natural Faltings/theta line bundle is not obtained. The natural theta divisor supplies a canonical effective section and a positivity mechanism, but it does not produce the required +80.55 Green term for the C9 uniform B=O_K profile, and it does not supply the object map from IUT complete C to A_g/Faltings moduli.

The exact situation:
- Standard theta/Faltings positivity is a conditional height inequality: if an arithmetic line bundle with a normalized effective theta section and semipositive metric has Arakelov degree equal to Q_C-h_C, then Q_C-h_C>=0 follows. This is a valid proof schema (Lemma 2.1/2.2), but all four required inputs (line bundle, section, metric normalization, equality) are missing from the source.
- For E_j, the natural Torelli/theta/Faltings height is of order log|j| or log|Delta|/12, about 20-56 natural units, not the 80.55 margin needed for B=O_K b=3; the exact theta height depends on a metric normalization that the source does not fix. This is an order-of-magnitude obstruction, not a theorem excluding every exotic metric.
- A metric/line-bundle twist could be chosen to force the degree, but that choice is arbitrary and prohibited. Theta divisor effectivity gives a divisor relation, not the C9 q-pilot/hull difference.
- The only known positivity statement survives from the IV container and the variational profile: B=O_K b=3 gives F>=80.55 under IV target containment. The theta divisor is not needed for that conditional statement and cannot upgrade it to a source theorem.

Thus the theta-divisor route is a genuine *conditional* positivity theorem schema plus an exact obstruction, not a proof of P6.

## 1. Arakelov/Faltings/theta setup

Let X be a proper arithmetic variety over Z (or O_F) of relative dimension g, with a Hermitian line bundle ar L=(L,||.||). For a section s of L with divisor div(s), the Arakelov degree/height of a point or cycle is

    h_{ar L}(x) = -log||s(x)|| + (intersection/Green terms),        (1.1)

with the standard adelic normalization. For an elliptic curve E over a number field, the Torelli map sends E to A_1 (moduli of principally polarized abelian varieties of dimension1); the theta line bundle Θ on A_g is ample and has a canonical theta section theta whose divisor is the theta divisor. Faltings' height h_F(E) is the Arakelov degree of the Hodge/theta line bundle on the moduli stack (Faltings, Moduli of abelian varieties, Invent. Math. 92 (1988)); up to the standard normalization, h_F is a theta-type height.

The C9 objects Q_C and h_C are not defined as such Arakelov degrees:
- Q_C is the native q-pilot global normalized log-volume from IUT;
- h_C is the normalized log-volume of the holomorphic hull of the union of Theta-pilot possible images;
- neither is defined by a line bundle on A_g or by a theta divisor. A comparison theorem from the IUT/Frobenioid/procession source to an Arakelov theta line bundle is missing.

## 2. Theta positivity lemma (standard/conditional)

Lemma 2.1 (effective-section positivity). Let ar L be a Hermitian line bundle on a proper arithmetic curve/stack with a nonzero global section s whose divisor is effective and whose metric satisfies the standard semipositivity and sup-norm normalization ||s||<=1 (or the corresponding adelic bound). Then the height/Arakelov degree contribution of s is nonnegative: -log||s||>=0, and the associated height of points not on div(s) is nonnegative; at div(s) it is +infinity. In particular an effective theta section gives a lower bound for the theta height.

Lemma 2.2 (Bost-Zhang positivity, as used). Bost-Zhang/Zhang arithmetic positivity gives lower bounds for heights of points/cycles under a nef/semipositive arithmetic line bundle and an effective section. It does not assert that an arbitrary Faltings/theta metric is semipositive, nor does it identify the resulting height with a q-pilot log-volume.

Conditional theorem schema (Theta-P6):
Assume there is a source functor C -> (X_C,ar L_C,s_C) with:
(T1) X_C a proper arithmetic model attached functorially to the complete C;
(T2) ar L_C a Faltings/theta-type Hermitian line bundle with semipositive metric;
(T3) s_C a nonzero effective theta-type section with ||s_C||<=1;
(T4) widehat{deg}(ar L_C)=Q_C-h_C (including the finite q-pilot and archimedean hull normalizations).
Then Q_C-h_C>=0, i.e. F(C)>=0.

Proof: (T3)+(T1/T2) give nonnegative height contribution by Lemma 2.1 (or Bost-Zhang); (T4) identifies the height with Q_C-h_C. This proves the positivity under the hypotheses. The theorem is not a proof of P6 because (T1)-(T4) are not established.

## 3. The natural E_j theta divisor and its numerical scale

For E_j: y^2=x^3+(3/M)x+(2/M), j=1/p^6, p=12301, M=1728p^6-1. The Torelli map sends E_j to A_1; theta divisor on A_1 is the cusp/point at infinity, and the theta/Faltings height is a function of the moduli j. With the standard normalization, the natural scale is:
- log|j| = 6 log p = 56.504615...;
- log|Delta|/12 = 21.941005... for the nonminimal discriminant; the Faltings height is a normalized version of this, up to constants.
These are order tens, not the 80.55 positive margin needed in the B=O_K b=3 profile (D_3-A_arc=80.5505776). The theta divisor's effective Green term is not a free constant: it is bounded by the theta/Faltings height modulo the chosen metric normalization. A different metric normalization can shift it by a constant, but that constant is not canonical and selecting it to produce +80.55 is arbitrary.

The sharper check for the B=I corridor: if B=I were actual and h_inf were of the order of a positive theta height (tens), then F=-S_3-h_inf would be strongly negative; the theta divisor would then support a counterexample, not a positivity theorem. But B=I is unproved and the actual h_inf is not the theta height. Thus theta data alone cannot decide the B=I corridor.

## 4. Where the theta proof attempt fails: exact obstructions

The proof attempt reduces to four lemmas, each of which fails for a precise source reason.

L1 (functorial line bundle). There is no source construction of a complete C -> arithmetic variety X_C with a Faltings/theta line bundle whose degree is Q_C-h_C. The IUT source produces processions/Frobenioid/Theta-pilot objects; the classical E_j->A_1 Torelli map uses only the elliptic curve, and it does not see the q-pilot/Theta-pilot hull, the weights, or the q/BPS/gluing data. No map from the IUT Hodge theater/procession to A_g is provided by the cited source. Status: MISSING/OBSTRUCTION.

L2 (effective theta section). A canonical theta section exists on A_g (and on A_1), but its divisor is the theta divisor, not the q-pilot/hull divisor. The C9 hull is a possible-image hull, not the zero divisor of a theta function; no source identifies them. Status: MISSING/OBSTRUCTION.

L3 (metric/semipositivity). Faltings/theta metrics are not known to be semipositive in the sense required by Bost-Zhang. The IV archimedean container gives an upper bound, not a semipositive metric/Green function. A canonical theta metric may have logarithmic singularities at the divisor; its pointwise norm is not the C9 h_inf. Status: CONDITIONAL/MISSING.

L4 (normalization/equality). Even if a theta height existed, the normalization of Q_C/h_C (B_I-zero, q-pilot, hull volume, weights) is not the Faltings/theta normalization. The finite q-pilot and the archimedean hull decomposition do not match the finite intersection/Green decomposition of a theta line bundle. No comparison theorem is known. Status: MISSING/OBSTRUCTION.

The four failures are not independent; L1 and L4 are the core: the theta divisor lives on a moduli space of abelian varieties, while Q_C-h_C is a log-volume of a source-specific complete-C output. Absent a functorial comparison, the equality (T4) is the whole problem, and choosing a line bundle/metric to enforce it is arbitrary.

## 5. The required +80.55 Green/effective term

The B=O_K b=3 profile needs F=D_3-h_inf>=80.55, with D_3=93.714971... and h_inf<=A_arc=13.164394... under IV. In a theta-divisor proof, the +80.55 would have to arise as a Green term -log||theta(E_C)|| (or a finite intersection) evaluated at the source point. The natural theta/Faltings height of E_j is of order log|j|=56.50 or log|Delta|/12=21.94, below 80.55 (with the standard normalization; the exact constants are metric-dependent). No source theorem says the source point lies at a theta-Divisor value with Green term >=80.55. Adding a constant/metric twist to reach 80.55 is an arbitrary normalization, prohibited.

For the B=I b=3 corridor (F<0 iff h_inf>-2.7563), a theta Green term of positive tens would indeed make F negative, but B=I is unproved. If B=I were actual, the theta-divisor route would not prove positivity; it would point toward a counterexample. This is the same negative corridor as task-245, now expressed height-theoretically.

For b=273, the local deficit is ~8834.7 even at h_inf=A_arc; no canonical theta term of that size exists from E_j (log|j|=56.5, log|Delta|/12=21.9). No theta positivity can close that row.

## 6. Could a different theta line bundle (not E_j) work?

One can formally twist ar L by any Hermitian line bundle M to force degree Q_C-h_C, and then use an effective section if one exists. This is not a construction:
- the twist M is arbitrary data not supplied by the source;
- an effective section of the twisted bundle is not known to exist; effectivity is not preserved by arbitrary twists;
- the metric on M changes the Green term, so one can force either sign; this is exactly the arbitrary r_v/normalization the task forbids.
Bost-Zhang positivity is preserved only under additional semipositivity/nef hypotheses, which are not established for the twist. Therefore twisting is not a proof; it is a restatement of the missing comparison.

## 7. What is proved / conditional / impossible

Proved/standard:
- Theta divisor on A_g is effective and ample; theta/Faltings heights are well-defined Arakelov invariants.
- Theta positivity lemma: an effective theta section with a normalized semipositive metric gives a nonnegative height contribution.
- For E_j, log|j|=56.5046 and log|Delta|/12=21.9410 (standard nonminimal); both are far below the 80.55 margin.
- The B=O_K b=3 positivity F>=80.55 survives from the IV container alone, without theta.

Conditional:
- Theta-P6 theorem: if a source functor and line bundle/section satisfying (T1)-(T4) exist, then P6 holds for that C. This is a proof schema, not a source theorem.
- If B=I and actual h_inf>-2.7563, the theta route points to F<0; but B=I/h_inf are missing.
- Bost-Zhang positivity could be applied only after semipositivity and comparison are supplied.

Impossible/withdrawn:
- Identifying Q_C-h_C with the E_j theta/Faltings height: no source map; numerical scales differ (order 20-56 vs 80.55 for B=O_K).
- Obtaining the +80.55 margin from the canonical theta divisor of E_j without a metric/twist: no source estimate; canonical scale too small.
- Proving P6 from theta effectivity alone: effectivity gives a height, not the q-pilot/hull difference.
- Any arbitrary twist/metric chosen to force degree: prohibited.

## 8. Exact theorem candidate and remaining obstruction

Theorem candidate (source height positivity):
For every admissible complete C, there exists a functorial arithmetic line bundle ar L_C with a canonical effective theta-type section s_C and semipositive metric such that
    widehat{deg}(ar L_C)=Q_C-h_C.
Then F(C)>=0 by Lemma 2.1/Bost-Zhang.

The exact remaining obstruction is the construction of ar L_C,s_C,metric and the comparison of their Arakelov degree with Q_C-h_C. No cited IUT/AbsTopIII/IV theorem supplies this comparison. The theta divisor on A_g is a natural positivity device, but the C9 functional is not a theta height; the required functor C->A_g with q-pilot/Theta-pilot compatibility is the missing source theorem.

A weaker conditional source theorem (archimedean only) is already available: under IV container and B=O_K b=3, F>=80.55; under B=I b=3, F<0 iff h_inf>-2.7563. The theta route adds no new unconditional positivity beyond these conditional statements.

## 9. Conclusion

The global height positivity theorem via a theta divisor is not proved. The natural theta/Faltings line bundle is effective and has a positivity mechanism, but it does not match Q_C-h_C, and its canonical height scale for E_j (order log|j| or log|Delta|/12) is below the required +80.55 for B=O_K b=3. A proof would require a new source functor from complete C/Theta-pilot to a theta line bundle with a metric/section whose Arakelov degree is exactly Q_C-h_C; this is missing. Twisting or choosing a metric to force the degree is arbitrary and forbidden. The B=I negative corridor remains the only known route to F<0, but B=I and actual h_inf are unproved.

Only C9-NEW-HEIGHT-POSITIVE-20261025.md written. Natural-language self-review done; no Lean/Project/kernel/comparator/independent review; no arbitrary data. target_accepted=false; P6 open.
