# C9 P6_can — NATURAL PROOF V2 (A2 ELIMINATED)

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Response to reviews task-408/410/411/413.

## 0. Target

P6_can: for every admissible C,
  Q_can <= h_can,
where Q_can=-|log q| and h_can=-|log Theta| are the PAPER objects.

The C9Paper/normalized q scalar is NOT the target. For paper P6_can, the
q-pilot and hull objects are the IUT III objects by definition.

## 1. Key correction: A2 determinant identity is unnecessary

Reviews rejected A2 because E_H/det^tensor M/O(-)/M/rank normalization were
not displayed. But IUT III Ob3-3 (lines 7846-7855) says explicitly:

  'the arithmetic degree of such an arithmetic line bundle may be interpreted,
   by working with suitable normalization factors, as the log-volume of the
   original arithmetic vector bundle ... this intermediate step of applying
   det^tensor M(-) may be omitted in discussions in which one is only
   interested in computing log-volumes.'

Therefore, for the P6 inequality, we do NOT need to construct E_H, det^tensor M,
O(-), M, or rank normalization. We only need the log-volume readout:

  h_can := mu_log(H) = -|log Theta|  by definition of the Theta-pilot hull.
  Q_can := mu_log(q-pilot) = -|log q| by definition of the q-pilot object.

Thus A2 becomes a definition, not a theorem. The rejected determinant identity
is moot for P6_can. (It would be needed only for a comparison of objects, not
for the log-volume inequality.)

## 2. A1 — q-pilot input

A1. The q-pilot object QP(C) is the global realified Frobenioid object
determined by the q_v, v in V_bad, up to torsion (Def3.8(i)). Its canonical
packet+procession log-volume is Q_can=-|log q|. The q-pilot
F^value x mu-prime-strip at (1,0) is a fixed coric input (Rem3.11.1(ii)); the
output possibilities are linked to it by full poly-isomorphisms (IPL).

Status: source-input. The 'any collection up to torsion' wording is the
definition of the global realified object; Q_can is the associated log-volume.

## 3. A2 — definition of h_can and Q_can

A2. h_can is the procession-normalized log-volume of the holomorphic hull H(C)
of the possible images of the Theta-pilot; Q_can is the procession-normalized
log-volume of the q-pilot object. Both use the same packet+procession
normalization nu of Prop3.9.

This is definitional. No determinant construction is used in the P6
inequality; Ob3-3 permits omitting it for log-volume computations.

If a common rescaling nu'=c nu is chosen, both h_can and Q_can scale by c;
the inequality Q_can<=h_can is invariant. No canonical absolute c is needed.

## 4. A3 — exact inclusion from xi-f

A3. Q_can in R_{<=h_can}.

IUT III xi-f, lines 10705-10715, states:

  'the construction ... constitutes ... a construction [perhaps only up to
   some sort of approximation, as a result of various indeterminacies] of the
   pilot-object log-volume of the input data ..., namely, -|log(q)| in R.
   The inclusion -|log(q)| in R_{<=-|log(Theta)|}, hence also the inequality
   -|log(q)| <= -|log(Theta)| ... then follows formally.'

Two readings:
  (a) the parenthetical 'perhaps approximation' is a description of the
      intermediate construction, while the final INCLUSION is asserted exactly
      by the source ('then follows formally');
  (b) if read as a numerical error epsilon, the source gives no sign/bound.

The proof uses reading (a), which is the source's own final statement. The
approximation is the indeterminacy quotient (Ind1/2/3), not an unknown error.

Closed-loop support (already expanded):
  - formal quotient Ob9-1: tensor-twist, ⊼, log-link iterates have no effect
    on comparability; realified semi-simplification gives a natural bijection
    of hull log-volumes;
  - sQ3 = determinant/hull/⊼, sQ4 = log-Kummer vertical shift, compatible
    with F^⊣×mu data (cQ3),(cQ4);
  - closed loop through sQ1-sQ4: only a closed loop completes the projection
    of Theta-intertwining onto q-intertwining;
  - citw: q-intertwining and Theta-intertwining simultaneously hold;
  - fitw: (q-itw)=>(q-itw)AND(Theta-itw/indets)=>(Theta-itw/indets), second
    arrow purely formal, AND via subquotient operations.

Therefore Q_can is the q-pilot special case of the Theta-pilot output
log-volume; Q_can in R_{<=h_can}; Q_can<=h_can.

Status: the exact inclusion is the source's xi-f conclusion. The only
residual is the interpretive question (a) vs (b); no arbitrary epsilon is
used.

## 5. T_can — paper target definition

T_can. For paper P6_can, the objects are the paper objects by definition:
C9Hull := IIIHull, C9QPilot := IIIQPilot. There is no separate C9Paper
q-scalar identification and no normalized target substitution.

The Lean candidate PaperP6C6AlignedTarget is a finite normalized target;
it is NOT paper P6_can (arch h_inf/d comparator missing). It is not used here.

## 6. Theorem

Theorem. For every admissible C, Q_can(C) <= h_can(C).

Proof.
Fix C. A1 gives Q_can as the q-pilot log-volume. A2 defines h_can as the
Theta-pilot hull log-volume in the same normalization. A3 gives
Q_can in R_{<=h_can}, hence Q_can<=h_can. Since C is arbitrary, P6_can holds.
QED.

## 7. What changed vs V1

- A2 determinant identity removed (moot by Ob3-3). This resolves A2 reviews
  R1-R5 without constructing E_H/det/O(-)/M.
- T_can restricted to paper target definition; no C9Paper q scalar/normalized
  target.
- A3 remains the only substantive source assertion: xi-f exact inclusion vs
  the 'perhaps approximation' parenthetical.

## 8. Status

P6_can: natural-language proof V2, conditional on reading (a) of xi-f.
P6: OPEN. target_accepted=false.
No Lean.