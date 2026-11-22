# Procession normalization: Remark 3.1.1(ii) weights and the F_l^x average

Date: 2026-10-28. Source analysis only. No Lean compilation and no Lean inequality.

This note records the exact normalized-weight formula of IUT III, Remark
3.1.1, (ii), and the exact j in F_l^x procession average used for
-|log(Theta)| in Theorem B and Corollary 3.12. It is written to replace the raw
SignedLabel sum model.

## 1. Source passages

- IUT III, Remark 3.1.1, (ii), pp.94-95 (extraction lines 5504-5562):
  normalized weights for log-volumes on the portion of log(alpha F_v)
  corresponding to K_v, and for direct sums over all v over a fixed v_Q.
- IUT III, Proposition 3.9, (i), p.116 (lines 7006-7011): procession
  normalization is the average over the capsules in the procession.
- IUT III, Theorem B, pp.21-22 (lines 1198-1229): -|log(Theta)| is the
  procession-normalized log-volume of the holomorphic hull of possible
  Theta-pilot images; the average is explicitly over j in F_l^x.
- IUT III, Corollary 3.12, pp.173-174 (lines 10499-10529): same definition.
- IUT III, Definition 3.8, (i), p.112 (lines 6731-6769): the Theta-pilot
  object is an object of prod_{j in F_l^x} (F_mod^circledast)_j.

## 2. Normalized weights: a single place

For v in V and a chosen v_Q in V_Q with v | v_Q, IUT III, Remark 3.1.1, (ii)
assigns to the portion of log(alpha F_v) corresponding to K_v the weight

  w_v  :=  1 / [K_v : (F_mod)_v].

This is the normalized weight for a single local summand. The normalization is
chosen so that multiplication by p_{v_Q} changes the log-volume by
+/- log(p_{v_Q}); the residue degree is divided out.

## 3. Normalized weights: a direct sum over all v over v_Q

When one considers the direct sum over all v in V lying over a fixed v_Q, the
normalized weight in Remark 3.1.1, (ii) is

  w_{v, v_Q}^{dir}
    :=  (1 / [K_v : (F_mod)_v])
        * ( sum_{w in V_mod, w | v_Q} [(F_mod)_w : Q_{v_Q}] ).

Here the sum over w is the sum of the local degrees of the base field over
Q_{v_Q}. Equivalently, for each local summand v the weight is w_v, and the
common factor sum_w [(F_mod)_w : Q_{v_Q}] restores the total Q_{v_Q}-degree.
Again the normalization makes p_{v_Q}-multiplication add or subtract
log(p_{v_Q}).

## 4. Normalized weights: tensor products

For a finite set A and places v_alpha | v_Q, alpha in A, the weight on the
tensor-product summand is

  w_A  :=  prod_{alpha in A} (1 / [K_{v_alpha} : (F_mod)_{v_alpha}]).

For the direct sum over all choices {v_alpha}_{alpha in A} of places over v_Q,
the normalized weight is

  w_{A, v_Q}^{dir}
    :=  ( prod_{alpha in A} 1 / [K_{v_alpha} : (F_mod)_{v_alpha}] )
        * ( sum_{ {w_alpha}_{alpha in A} }
              prod_{alpha in A} [(F_mod)_{w_alpha} : Q_{v_Q}] ).

The sum is over all collections {w_alpha} of elements of V_mod over v_Q,
indexed by A; the w_alpha need not be distinct (Remark 3.1.1, (ii), lines
5547-5555). This is the exact tensor-version of the preceding formula.

## 5. Exact F_l^x procession average

By Definition 3.8, (i), the Theta-pilot object is an object of

  prod_{j in F_l^x} (F_mod^circledast)_j.

By Theorem B and Corollary 3.12, -|log(Theta)| is the procession-normalized
mono-analytic log-volume of the holomorphic hull of the union of the possible
images of this object. The procession average is taken over j in F_l^x. Hence,
in the finite case,

  -|log(Theta)|
    = (1 / |F_l^x|) *
      sum_{j in F_l^x}
        mu_log^{proc}(
          Hull(
            union_{possible images}
              pi_j( Theta-pilot )
          )
        ),

where

- pi_j is the j-th component of the multiradial representation of
  Theorem 3.11, (i), (a);
- the union is over the possible images subject to (Ind1), (Ind2), (Ind3);
- Hull is the holomorphic hull in the j-th IQ capsule;
- mu_log^{proc} is the packet-normalized mono-analytic log-volume after the
  procession normalization of Proposition 3.9, (i), (ii);
- |F_l^x| = l - 1, not l.

This is the exact averaging range. It is an average over the multiplicative
group F_l^x, not over the project's SignedLabel type.

## 6. Expanded local form

If the hull log-volume at label j is written as a sum of normalized local
contributions,

  mu_log^{proc}(Hull(union possible images)_j)
    = sum_{v in V_bad} sum_{alpha in A_v}
        w_{v,alpha} * ell_{j,v,alpha},

with the weights w_{v,alpha} as in Sections 2-4, then the exact global
formula is

  -|log(Theta)|
    = (1 / (l - 1)) *
      sum_{j in F_l^x}
        sum_{v in V_bad} sum_{alpha in A_v}
          w_{v,alpha} * ell_{j,v,alpha}.

Equivalently, exchanging the finite sums,

  -|log(Theta)|
    = sum_{v in V_bad} sum_{alpha in A_v}
        w_{v,alpha} *
          ( (1 / (l - 1)) * sum_{j in F_l^x} ell_{j,v,alpha} ).

Thus the j-average is an average over the full F_l^x, and the v-sum is weighted
by the Remark 3.1.1, (ii) weights. The two operations are not interchangeable
with an unweighted sum over V_bad, and neither is a sum over SignedLabel.

## 7. Theta values and labels: what is and is not averaged

The local theta values are

  { q_{j,v}^2 }_{j=1,...,l^*},  v in V_bad,

with l^* = (l - 1)/2 (IUT III, pp.16-17, lines 898-902; IUT II, pp.2-3, lines
69-108; Remark 2.5.1, pp.72-73, lines 4356-4396). These are values up to the
mu_{2l}-orbit: q_{j,v}^2 and q_{-j,v}^2 represent the same theta value.

The Theta-pilot product and the procession average, however, use the full label
set F_l^x (Definition 3.8, (i); Theorem B; Corollary 3.12). The l^* values are
representatives of the theta values; they are not the full index set for the
procession average. One must not replace:

- the F_l^x average by a sum over l^* positive representatives;
- the F_l^x average by a sum over SignedLabel l.value (cardinality l, with 0
  and both signs);
- the theta values by the raw powers q_v^{j^2} and then average their real
  logarithms as if the hull log-volume were linear.

The exact source average is over the label product F_l^x, with the theta
values/theta monoids as input to the hull; it is not a raw average of the real
numbers q_v^{j^2}.

## 8. Relation to the q-pilot side

The q-pilot object of Definition 3.8, (i), is an object of the global realified
Frobenioid C_Delta^vdash, determined by the q_v at v in V_bad. Its
procession-normalized mono-analytic log-volume -|log(q)| uses the same
normalized weights w_v of Sections 2-4 on the local q contributions, and the
procession normalization of Proposition 3.9, (i). It does not carry the
F_l^x product of the Theta-pilot object in the same literal way; the q-pilot is
a global q-family object. The precise q-side formula is recorded in
GlobalQPilotNormalization.md.

The source comparison

  -|log(Theta)| >= -|log(q)|

therefore relates:

- a weighted, holomorphic-hull, F_l^x-averaged Theta-side volume;
- a weighted, procession-normalized q-family volume;

not a raw SignedLabel theta sum and not an unweighted bad-place q sum.

## 9. The raw SignedLabel model, explicitly rejected

The raw model used in some candidate files is

  G = sum_{b in V_bad} (1 / card(SignedLabel l.value))
        * sum_{j in SignedLabel l.value}
            ( - log( (baseQReal b)^(gaussExponent j.1) ) ).

This is structurally different from the source formula in Sections 5-6:

1. the label set is SignedLabel (cardinality l, includes 0), not F_l^x
   (cardinality l - 1);
2. there is no holomorphic hull and no union of possible images;
3. there is no multiradial representation and no Ind1/Ind2/Ind3;
4. the local theta-value logs are used linearly instead of through the theta
   monoids/hull log-volume;
5. the local q contributions are summed unweighted, not with the
   Remark 3.1.1, (ii) normalized weights;
6. the sign is the positive raw magnitude, whereas -|log(Theta)| is the
   non-positive hull volume.

For l = 5, G has coefficient

  0^2 + 1^2 + 2^2 + 1^2 + 2^2 = 10,  10/5 = 2,

while the F_l^x raw average of j^2 would have coefficient

  1^2 + 2^2 + 3^2 + 4^2 = 30,  30/4 = 7.5.

Neither is the source procession normalization; the coefficient 2 is only a
diagnostic of the SignedLabel raw model.

## 10. Correct formula summary

Let J = F_l^x and |J| = l - 1. Let

  L_j := mu_log^{proc}(
    Hull( union_{possible images} pi_j(Theta-pilot) )
  ),

with the Remark 3.1.1, (ii) local weights and the Proposition 3.9 procession
normalization. Then

  -|log(Theta)| = (1 / |J|) * sum_{j in J} L_j,

and, if L_j = sum_{v,alpha} w_{v,alpha} ell_{j,v,alpha},

  -|log(Theta)|
    = sum_{v,alpha} w_{v,alpha}
        * ( (1 / |J|) * sum_{j in J} ell_{j,v,alpha} ).

This is the exact normalization pattern: weighted local log-volumes, then the
F_l^x procession average. No raw SignedLabel sum appears.

## 11. References

- IUT III, Remark 3.1.1, (ii), pp.94-95: extraction lines 5504-5562.
- IUT III, Proposition 3.9, (i), p.116: lines 7006-7011.
- IUT III, Definition 3.8, (i), p.112: lines 6731-6769.
- IUT III, Theorem B, pp.21-22: lines 1198-1229.
- IUT III, Corollary 3.12, pp.173-174: lines 10499-10529.
- IUT III, Introduction, pp.16-17: lines 888-908.
- IUT II, Introduction, pp.2-3: lines 69-108.
- IUT II, Remark 2.5.1, pp.72-73: lines 4356-4396.
- Project candidate definitions:
  tmp/sheaf/xif/paper/GlobalThetaPilotLogVolumeActual.lean,
  localThetaLogVolume / globalThetaPilotLogVolume.
- Project q-side analysis: tmp/sheaf/xif/paper/GlobalQPilotNormalization.md.
- Project signed procession: tmp/sheaf/xif/paper/PaperSignedHullSignedActual.lean,
  c3ThetaSignedProcession.
