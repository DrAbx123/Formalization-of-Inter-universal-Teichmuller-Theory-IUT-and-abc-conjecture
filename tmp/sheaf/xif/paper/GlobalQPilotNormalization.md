# Global q-pilot log-volume: source normalization vs sourceQPilotSignedLog

Date: 2026-10-28. Analysis only; no Lean compilation.

## 1. What the source actually defines

### 1.1 q-pilot object

IUT III, Definition 3.8, (i), p.112 (extraction lines 6731-6769):

- the Theta-pilot object is the object of
  `prod_{j in F_l^x} (F_mod^circledast)_j` determined by generators of the
  local monoids at v in V_bad;
- the q-pilot object is the object of the **global realified Frobenioid**
  `C_Delta^vdash` of IUT II, Corollary 4.10, (i), determined by a collection,
  indexed by v in V_bad, of generators up to torsion of the splitting monoid
  associated to `F^vdash_{Delta,v}`; concretely, by the q_v.

IUT III, Introduction, p.16 (lines 880-893) says the q-pilot object is the
object obtained from the arithmetic divisor determined by the zero locus of the
elements q_v at v in V_bad, and its log-volume is denoted

  -|log(q)| in R,   |log(q)| > 0.

So the source q-pilot is a **global object of C_Delta^vdash**, not the
theta-label-1 scalar and not a single local q_v.

### 1.2 The scalar is procession-normalized

IUT III, Theorem B, p.21-22 (lines 1198-1229) and Corollary 3.12, p.173-174
(lines 10499-10529):

- `-|log(Theta)|` is the **procession-normalized mono-analytic log-volume**
  of the holomorphic hull of the possible Theta-pilot images; the average is
  explicitly over j in F_l^x (lines 1204-1207 and 10504-10507);
- `-|log(q)|` is the **procession-normalized mono-analytic log-volume of the
  image of a q-pilot object** in the multiradial representation (lines
  1213-1217 and 10516-10521).

The meaning of "procession-normalized" is fixed in Proposition 3.9, (i),
p.116 (lines 7006-7011):

> when working with collections of capsules in a procession ... log-volumes on
> the products ... are normalized by taking the average, over the various
> capsules under consideration; we shall refer to this normalization as the
> procession-normalization.

Thus `-|log(q)|` is **not by definition a raw sum over v**. It is an average
over the capsules of the procession of the q-pilot image. If the q-pilot
contribution is the same in every capsule, the average collapses to that common
contribution; the source does not display a separate 1/|F_l^x| in the q-pilot
formula. The source gives the average rule, not a bare-sum rule.

### 1.3 Local q log and normalized weights

IUT III, Remark 3.9.1 context, p.125 (lines 7601-7607):

  log(q) = ord_v(q_v) * log(p_v) in R.

This is the local q log at a place v. IUT III, Remark 3.1.1, (ii), p.94-95
(lines 5504-5562) fixes the normalization of local log-volumes: on the part of
log(alpha F_v) corresponding to K_v one uses the weight

  1 / [K_v : (F_mod)_v],

and for direct sums over all v over a fixed v_Q the normalized weight

  (1 / [K_v : (F_mod)_v]) * (sum_{V_mod contains w | v_Q} [(F_mod)_w : Q_{v_Q}]).

The weight is chosen so that multiplication by p_{v_Q} changes log-volume by
+/- log(p_{v_Q}), not by the residue degree. Hence the global q-pilot
log-volume is a **weighted** sum of local q logs, not an unweighted sum over
places.

### 1.4 V_bad indexing

IUT I, Definition 3.1, (b), (e), p.61-62 (lines 3194-3229, 3280-3290):

- V_bad is the set of nonarchimedean valuations of F over the chosen nonempty
  V_bad,mod;
- V is a section of V(K) -> V_mod.

The q-pilot collection is indexed by the actual v in V_bad, one local q_v for
each such v. There is no extra theta-label average in the index set itself.

## 2. Reconstructed global formula

Combining 1.3 and 1.4, the q-pilot log-volume before the procession average is
the weighted sum of the local q logs:

  log(q)_global = sum_{v in V_bad} (1 / [K_v : (F_mod)_v])
                    * ord_v(q_v) * log(p_v).

Since the local q-parameters are contracting (the project source has
q_parameter_contracting: ||q_b|| < 1, hence log(q_v) < 0), the absolute value is
the sum of the absolute local logs:

  |log(q)|_weighted = sum_{v in V_bad} (1 / [K_v : (F_mod)_v])
                        * |log(q_v)|,

where |log(q_v)| is the normalized local absolute log, i.e. the absolute value
of ord_v(q_v) log(p_v), not an arbitrary real norm of q_v.

Therefore the reconstructed paper scalar is

  -|log(q)| = - sum_{v in V_bad} (1 / [K_v : (F_mod)_v]) * ord_v(q_v) log(p_v)

and its magnitude is the weighted sum above. The procession normalization is an
average over the capsules of the q-pilot image; with the q-pilot image carrying
the same global q contribution in each capsule, it introduces no further factor
in this scalar. If the source representation distributes the q-pilot object
non-diagonally over the capsules, the average must be applied explicitly; the
source formula is the average, not the raw sum.

Caveat: IUT III Corollary 3.12 does not display this weighted sum as a single
formula; it says only that |log(q)| "is easily computed in terms of the various
q-parameters ... at v in V_bad" (lines 1225-1227 and 10525-10527). The weighted
formula is the reconstruction from Definition 3.8, (i), Remark 3.1.1, (ii), and
Proposition 3.9, (i), not a verbatim display in Corollary 3.12.

## 3. What sourceQPilotSignedLog actually is

In the project tree:

  sourceQPilotSignedLog S
    = - sum_{b : S.badPlaces} |Real.log (S.reduction.qParameter b)|

and

  sourceBadQAbsLog S
    = sum_{b : S.badPlaces} |Real.log (S.reduction.qParameter b)|.

This is:

- an **unweighted** sum over S.badPlaces;
- using the real norm log |log ||q_b|||, not the normalized local log
  ord_v(q_v) log(p_v) with the [K_v : (F_mod)_v]^{-1} weight;
- with no procession average and no q-pilot global realified Frobenioid object;
- a negative scalar whose magnitude is the unweighted bad-place absolute-log
  sum.

It is therefore **not the paper global q-pilot log-volume in general**. It is
an unweighted bad-place surrogate.

## 4. Exact comparison

Let

  W_v := 1 / [K_v : (F_mod)_v],  v in V_bad,

and let log_norm(q_v) be the normalized local log ord_v(q_v) log(p_v). Then the
paper magnitude is

  |log(q)|_paper = sum_{v in V_bad} W_v * |log_norm(q_v)|

(up to the explicit procession average if the q-pilot image is not diagonal),
whereas the project scalar has magnitude

  |log(q)|_Lean = sum_{b : S.badPlaces} |Real.log ||qParameter b|||.

Hence

  sourceQPilotSignedLog S = -|log(q)|_paper

holds exactly only under all of the following extra identifications:

1. S.badPlaces is exactly the source index set V_bad (all bad places, with the
   same cardinality/indexing), not a different abstract bad-place type;
2. all normalized weights are one: [K_v : (F_mod)_v] = 1 for every v in V_bad;
3. Real.log ||qParameter b|| equals the normalized local log
   ord_v(q_b) log(p_b) (the norm and residue-degree normalizations agree);
4. the procession normalization of the q-pilot image is diagonal, so no
   additional capsule average remains.

Without 1-4, the correct relation is a weighted sum, and the Lean scalar differs
by the weight factors and the local-normalization convention. In particular,
the Lean scalar has no place for the source weights W_v, so it cannot be the
paper global q-pilot scalar in general.

## 5. Relation to C3.q

In the project, the paper local scalar candidate is

  localSignedLog C3.q = Real.log ||C3.q.q||,

a single completion q candidate. This is one local q, not the global q-pilot
object. The identification

  sourceQPilotSignedLog I.initial = localSignedLog C3.q

is therefore an extra source-q identification: it says the unweighted bad-place
sum equals the log norm of the single C3 completion q. It does not follow from
the paper's global weighted sum unless C3.q is itself the aggregate q whose
signed log is the weighted bad-place sum and all weights/normalizations
coincide.

Equivalently, the correct relation between the global paper q-pilot scalar and
C3.q would require

  Real.log ||C3.q.q||
    = - sum_{v in V_bad} (1 / [K_v : (F_mod)_v]) * ord_v(q_v) log(p_v)

(up to the procession average), not the unweighted Lean sum. This is the exact
normalization missing from the current sourceQPilotSignedLog.

## 6. Bottom line

1. Corollary 3.12 defines -|log(q)| as the **procession-normalized mono-analytic
   log-volume** of the q-pilot image, not as an unweighted sum.
2. The local q log is ord_v(q_v) log(p_v); the global q-pilot scalar uses the
   normalized weights 1/[K_v:(F_mod)_v] from Remark 3.1.1, (ii), and the
   procession average from Proposition 3.9, (i).
3. The raw formula -sum_v |log q_v| is correct only in the special case where
   all weights are 1 and the q-pilot image is diagonal under the procession
   average; it is not the general paper scalar.
4. sourceQPilotSignedLog = -sum_{b : badPlaces} |log ||q_b||| is the
   unweighted, unnormalized bad-place surrogate. It captures the negative sign
   and the bad-place absolute-log sum, but it is not the paper global q-pilot
   log-volume unless the four identifications in Section 4 hold.
5. There is no extra division by the theta-label cardinality in the q-pilot
   scalar itself: the q-pilot object is not the Theta product over
   j in F_l^x. The procession average is a capsule average; for a diagonal
   q-pilot image it collapses, and for a non-diagonal image it must be applied
   explicitly. It is not the same thing as dividing the bad-place sum by
   |F_l^x|.

## 7. References

- IUT III, Definition 3.8, (i), p.112: extraction lines 6731-6769.
- IUT III, Introduction, pp.16-17: lines 880-893, 949-961.
- IUT III, Theorem B, pp.21-22: lines 1198-1229.
- IUT III, Corollary 3.12, pp.173-174: lines 10499-10529.
- IUT III, Proposition 3.9, (i), p.116: lines 7006-7011.
- IUT III, Remark 3.1.1, (ii), pp.94-95: lines 5504-5562.
- IUT III, local log(q) formula, p.125: lines 7601-7607.
- IUT I, Definition 3.1, (b), (e), pp.61-62: lines 3194-3229, 3280-3290.
- Project definition: tmp/sheaf/xif/paper/ConcreteSourceQIdentificationActual.lean,
  theorem sourceQPilotSignedLog_eq_neg_sum_abs_log.
- Project local q scalar: tmp/sheaf/xif/PaperQPilotLogVolume.lean,
  paperQPilotLogVolume_eq_log_norm.
