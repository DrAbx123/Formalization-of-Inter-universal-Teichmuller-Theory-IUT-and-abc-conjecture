# IND2-REVIEW — independent check of ind2Term in the unramified e=1 model

Status: READ-ONLY source review, 2026-11-12. No compile, no Lean claim.
Sources: Iut/WallEquiv/Gap.lean:747 (ind2Term), Gap.lean:594/624/639
(lgpComp/gapTerm), ThetaRegion.lean:126/136/170/257/261, IndAut.lean:210/219,
LogShell.lean:174/193, Theory.lean:337 (shell_eq_integral), VcI.lean:529/603
(leastHull_tensorLogShell_eq, componentVol_leastHull...), Gap.lean:756
(ind2Term_nonneg), Gap.lean:523 (gap_eq_rhs_add), VcI.lean:725/741.

## 0. Definitions

For a finite rational place p, capsule i, component c, and label
j = i+1:

  a := D.scaleElt (nC D) i p c
     = incl_j (qroot_{v_j}^{j^2})              (ThetaRegion:136)
  S := LocalTheory.shell D.Kt p (tuple D.placeSect _ c)
  L := LocalTheory.leastHull (.finite p) (tuple ...) S
  theta := D.thetaComponent (nC D) i (.finite p) c
  Htheta := LocalTheory.leastHull (.finite p) (tuple ...) theta

  ind2Term := V(Htheta) - V(a • L)              (Gap:747)

where V = componentVol. The source thetaComponent uses ivLabels, which is the
singleton {j} (ThetaRegion:237, 257), and thetaFinite_eq says

  theta = ⋃ φ ∈ tensorAut, φ '' (a • S)          (ThetaRegion:261)

with a = scaleElt (the distinguished label j only). The literal reading
(litLabels = all labels) is a different region, used by rhsDataLit, not by
ind2Term.

## 1. Unramified e=1 model

Assume p odd, every factor place is finite of residue characteristic p, and
ramIdx = 1. Then:
1. factorLogShell = closed unit ball / integral lattice
   (LogShell.lean:193, factorLogShell_eq_of_unramified);
2. shell S = integral O (Theory.lean:337, shell_eq_integral);
3. leastHull of O is O (leastHull_tensorLogShell_eq, VcI:529/603 with maximal
   norm element 1), so L = O;
4. qroot is an element of the completion (Data.lean:142/327-330,
   qrootOf : completionAt), hence its ord_p is an integer;
   x := j^2 * ord_p(qroot) is an integer. Write x = m (integer);
5. a is a nonzero field element of the tensor algebra; a•O = p^m O as a
   Z_p-lattice (fractional lattice), and
   V(a•O) = -m log p = -j^2 * v_p(q) log p / (2 l) = -j^2 A,
   where A := v_p(q) log p / (2 l). (componentVol_units_smul +
   componentVol_prime_preimage'; equivalently the scaling law.)

Now tensorAut. An element φ ∈ tensorAut is a tensor product of factor
Z_p-lattice automorphisms preserving the factor log-shell (IndAut.lean:210/219).
For e=1 the factor log-shell is O, hence φ(O)=O and, because φ is Z_p-linear,
φ(p^m O)=p^m O for every integer m. Therefore:

  φ '' (a • O) = φ '' (p^m O) = p^m O = a • O   for every φ.

Thus the union in theta is exactly a•O, and Htheta = a•O. Consequently:

  ind2Term = V(a•O) - V(a•O) = 0.

This is the exact e=1 unramified answer: no Ind2 enlargement, no floor/frac;
the theta component does not exceed the scaled lattice. The volume is -j^2 A
(not -A unless j=1; with ivLabels there is only one label j, not a minimum over
l).

## 2. What if S is the literal all-labels set?

If one replaces ivLabels by litLabels = all labels (this is rhsDataLit, not
ind2Term), the union contains a_l • O for l = 1,...,nC. With a_l = qroot^{l^2},
a_l•O = p^{l^2 m}O. These lattices are nested: larger l gives a smaller lattice.
The union is the largest one, l = 1, i.e. p^m O = a_1•O; leastHull of the union
is p^m O and

  V(leastHull(all-labels theta)) = -A.

Against lgpComp = a_j•O = p^{j^2 m}O this gives a positive linear difference
(j^2-1)A, not a fractional part. But this is NOT the source ind2Term: ind2Term
uses thetaComponent (ivLabels singleton). Do not mix the two regions.

## 3. Comparison with the C0 frac formula

C0 proposed ind2Term = frac(j^2 v_p(q)/(2l)) * log p. In the e=1 model:
- qroot exists in the completion, so its ord_p is an integer;
- qOrder = v_p(q) and ord_p(qroot) = qOrder/(2l) must be an integer;
- therefore j^2 qOrder/(2l) is an integer and frac = 0.
So C0's formula is consistent with ind2Term = 0 in this model; it is vacuous here.
A nonzero ind2Term cannot arise from a fractional part of v_p(q)/(2l) in a
discretely valued completion: fractional valuations do not exist for elements of
the completion. Nonzero Ind2 requires a genuinely different mechanism:
- ramified/wild shell S ≠ O (then a•S is not a scalar p^m O and φ need not
  preserve it);
- tensorAut images not equal because φ is only Z_p-linear, not multiplicative;
- or a different theta set (literal labels), which is a different object.
The C0 frac formula does not establish any of these; it only gives zero under the
integrality forced by qroot.

## 4. Self-consistency checks

1. ind2Term_nonneg (Gap:756): our value 0 satisfies 0 <= 0. The source proof
   uses lgpComp_subset_theta and componentVol_le_leastHull; at e=1 both sides
   coincide, so equality is consistent.
2. gapTerm_finite (Gap:780): gapTerm = shellDefect + ind2Term. At e=1 odd
   unramified, shellDefect=0 (Gap:447), so gapTerm=0. This is consistent with
   gapHullAt=0 at such a finite place (Gap:895/919) and with gap support away
   from good finite places.
3. gap_eq_rhs_add (Gap:523) is an identity:
   gap = rhs + sFactor(nC)*A - V(hull VC).
   Setting one local ind2Term to zero does not contradict it; the gap comes from
   the remaining local terms (other primes, arch, wild/ramified), and the
   identity is algebraic.
4. ind2Term_eq_zero (Gap:771) is stated for p not in badChars, not for the
   present bad e=1 case. Our zero is a model computation, not the source's
   nonbad theorem.
5. The volume of the theta hull in the e=1 singleton case is -j^2 A, while the
   LGP component a•O has the same volume; there is no enlargement. In the
   literal all-labels case the hull is -A and the difference from a_j is
   (j^2-1)A, positive linear. Neither produces a fractional-part term.

## 5. Verdict

- For the source ind2Term with ivLabels and unramified e=1 odd:
  theta = a•O, Htheta = a•O, ind2Term = 0 exactly.
- The answer is not q^{jmin^2}O for the source object: with ivLabels there is one
  label j=i+1 and the volume is -j^2 A. For the literal all-labels object the
  hull is q^{1^2}O and the volume is -A, but that is rhsDataLit, not ind2Term.
- Ind2 does not enlarge the volume in this model; frac/floor is zero. The C0
  frac formula reduces to 0 because a completion element has integer valuation.
- Nonzero Ind2, if it exists, must come from ramified/wild shell geometry or
  non-multiplicativity of tensorAut, not from a fractional q-order. The source
  leaves that case open; our e=1 computation does not prove the general case.

No Lean file is written; no compile is claimed.
