# C9 P6_can NATURAL PROOF — SELF-AUDIT

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Audit of C9-P6-CAN-NATURAL-PROOF-20261025.md.

## 0. Verdict

The proof is logically valid as a source-construction proof IF the
A1-A3/T_can source statements are accepted as proof steps. It is NOT yet
an unconditional first-principles proof: several steps are source-level
construction statements, not expanded algebra.

## 1. A1

Statement: q-pilot object determined by q_v up to torsion; Q_can well-defined.
Source: Def3.8(i), Rem3.11.1(ii).

Risk: Def3.8(i) says 'the object ... determined by any collection ... of
generators up to torsion'. The word 'any' is read as choice-independence of
the resulting global realified Frobenioid object. This is a definitional
reading; source does not display a separate independence lemma.
Status: accepted as source definition; flag F1.

## 2. A2

Statement: E_H rank>1 arithmetic vector bundle; L_H=det^tensor M(E_H) tensor
det^tensor M(O(-))^{-1}; deg(L_H)/M=mu_log(H)=h_can; deg(L_q)=Q_can.
Source: Ob1-Ob3, Prop3.9(iii), Ob3-2, Ob3-3.

Risk: the explicit construction of E_H and the determinant/degree identity
are source construction steps; the ratio identity is stated in a common
normalization, and the source supplies only 'suitable normalization' language.
Status: accepted as ratio identity; flag F2 (absolute canonical identity open).

## 3. A3

Statement: Q_can in R_{<=h_can}.
Source: Ob9-1/Ob9 (formal quotient), sQ3/sQ4 cQ3/cQ4, closed loop,
citw/fitw AND.

Risk: CL1-CL3 are expanded to source statements, but the subquotient
AND/realified semi-simplification operations are not displayed as
set-theoretic maps. The proof does not introduce an epsilon.
Status: accepted as source closed-loop construction; flag F3 (formal
encoding of subquotient operations).

## 4. T_can

Statement: C9Hull=IIIHull, C9QPilot=IIIQPilot for paper target.
Risk: this is the paper target object definition. If C9 uses independently
defined objects, T_can needs a comparator; the normalized Lean target is
NOT equivalent to paper P6_can (arch h_inf/d).
Status: definitional for paper P6_can; flag F4.

## 5. Final inference

From A2: h_can is log-volume of the Theta hull; Q_can is log-volume of the
q-pilot. From A3: Q_can in R_{<=h_can}. By definition of R_{<=h_can}, this
is Q_can<=h_can. This inference is exact.

## 6. What would make the proof unconditional

Expand F1 (choice-independence of QPilot), F2 (explicit E_H/det/degree
identity), F3 (subquotient/realified-semi-simplification operations),
F4 (paper target object identity). These are source construction details,
not new assumptions and not numerical epsilon.

## 7. Status

Natural-language proof: source-construction complete.
Unconditional first-principles proof: not yet; F1-F4 are source-level
construction details.
P6_can: conditional on F1-F4 acceptance.
P6: OPEN. target_accepted=false.