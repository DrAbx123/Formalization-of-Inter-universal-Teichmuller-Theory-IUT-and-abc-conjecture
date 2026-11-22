# C9 CANONICAL A3 — EXCLUDED WRONG ROUTES

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Target: A3 for paper P6_can:
  Q_can = -|log q| in R_{<= h_can},  h_can = -|log Theta|.

Purpose: list routes already tried/checked and why they do NOT prove A3.

## 0. Surviving route

Surviving route: xi-f + Remark3.12.2(fitw) logical relation:
  (q-itw) => (q-itw) AND (Theta-itw/indets) => (Theta-itw/indets),
with '/indets.' = up to (Ind1),(Ind2),(Ind3); the second arrow purely
formal; the AND from the (citw) AND via Remark3.9.5(viii) subquotient
operations. Then Q_can is a special case of the Theta-pilot output
log-volume; exact membership in R_{<=h_can}.

Residual exact gap: expand the subquotient AND/operations of Remark3.9.5(viii).

## 1. Excluded routes

E1. Numerical epsilon route.
  Treat 'perhaps up to approximation' as Q_can + epsilon in R with unknown
  epsilon. Source gives no sign and no bound. Choosing epsilon=0 or epsilon<=0
  is arbitrary. EXCLUDED (task-393/402).

E2. Normalize by d / replace paper target by P6_norm.
  Divide h_can by d=41 or use C6 normalized h_C to turn A3 into
  Q_norm<=h_C. That changes the target; arch h_inf is not divided by d.
  EXCLUDED (task-395/399/400).

E3. Mixed target Q_can<=h_C.
  Off by d and arch term. EXCLUDED (task-383/395/400).

E4. Rescue P6_norm by h_inf>=0 / B_I subset H_C,inf.
  h_inf>=0 is not a source theorem; B_I is not proved an arch possible
  image. This is an extra arch hypothesis, not A3. EXCLUDED (task-363/368/371).

E5. Use mixed bad/good profiles or row max.
  Mixed profiles are E3 profile change, not possible images of fixed uniform C.
  Row max is the wrong normalization; target readout is weighted average.
  EXCLUDED (task-303/304/305/310/311/313, correction notes).

E6. Use q_v scalar / full q=qhat^{82}.
  q-pilot uses qhat with 2l=82 root normalization; full q adds factor 82.
  q_v is only up to torsion; no canonical scalar. EXCLUDED (task-390, task-401).

E7. Treat 0,circ U = 1,circ U as canonical equality/section.
  It is a noncanonical permutation symmetry; compatibility with hull/det/
  log-volume is asserted, not a canonical identification. EXCLUDED (task-373/396).

E8. Use geometric hull/max/union volume instead of log-volume set.
  R_{<=h_can} is a set of possible log-volumes, not a geometric union measure.
  EXCLUDED (task-319/320 and max-row retraction).

E9. Use C1 residual F<=D-h_inf to prove A3.
  C1 is a lower bound on h_C, hence upper bound on F; it cannot give
  Q_can in R or Q_can<=h_can. EXCLUDED (E48 sign correction).

E10. Use b=273 no-go/counterexample to bypass A3.
  The b=273 no-go is retracted; counterexample route needs explicit C and
  JP/G1/U, none of which proves A3. EXCLUDED (task-256/E48, task-301/302).

E11. Use global unit/point in H_C,inf or product formula pointwise.
  No canonical global point/unit in the hull is known; product formula is
  pointwise, not a hull-volume lower bound. EXCLUDED (task-270/349/361).

E12. Use 'source says approximation, so take limit/closure epsilon->0'.
  No source bound/sign on the error; closure of R does not imply the exact
  value lies in R. EXCLUDED (task-402/405).

E13. Use canonical absolute A2 value as an input to A3.
  Canonical absolute -|logTheta| is not fixed; only ratio in a common
  normalization. A3 membership is scale-invariant but does not supply a
  canonical absolute c. EXCLUDED (task-401).

E14. Use Lean candidate PaperP6C6AlignedTarget as paper A3.
  It is a finite normalized target without arch; not equivalent to paper
  P6_can; comparator differs by h_inf/d. EXCLUDED (task-404).

## 2. Consequence

Only surviving A3 route: fitw logical relation + subquotient AND.
All numerical-epsilon, normalization-factor, mixed-profile, row-max,
arch-containment, C1-sign, counterexample, and Lean-normalized routes are
excluded as proofs of paper A3.

P6_can still conditional on expanding the subquotient AND.
P6: OPEN. target_accepted=false.