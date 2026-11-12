# S1642: evaluated nonsingularity and zero-class criterion — exact first missing

Date: 2026-10-31.

## Actual input from S1626

S1626 has:

- s1626RingEval : Universal.Ring ->+* R, ring hom;
- s1626CurveRing.map (s1626RingEval W eqn) = W;
- smulEval = evalEval x y o ![phi,omega,psi];
- s1626RingEval_comp_smulRing;
- s1626ZSMulPointEqSmulEval:
  (n • P).toJacobian.point = class (smulEval W x y n).

## First missing lemma: evaluated nonsingularity

S1626 has field-level nonsingularity:

  s1626Nonsingular_smulField n :
    pointedCurve.toJacobian.Nonsingular (smulField n)

It does NOT have the Universal.Ring-level statement

  s1626Nonsingular_smulRing n :
    s1626CurveRing.toJacobian.Nonsingular (smulRing n)

nor the evaluated statement

  s1626Nonsingular_smulEval (W) (eqn) n :
    W.toJacobian.Nonsingular (s1626SmulEval W x y n).

Deriving evaluated from field via map_nonsingular is not direct: the
available map is from s1626CurveRing to W along s1626RingEval, so one first
needs ring-level nonsingularity.  Field-level does not descend to the ring
automatically.

## Second missing lemma: zero-class criterion

For a Jacobian representative P with a nonsingularity proof, the needed lemma is

  class P = 0  <->  P 2 = 0,

i.e.

  (class (s1626SmulEval W x y n) = 0) <-> s1626SmulEval W x y n 2 = 0.

Forward: class zero is represented by ![1,1,0]; if P is equivalent by scalar
u, then P 2 = u * 0 = 0.

Backward: P 2 = 0 gives Z=0; one must show class is zero, using
nonsingularity to exclude other Z=0 projective classes.  Without Nonsingular P
the statement is false in general.

So the exact second field is the class-zero/Z-coordinate lemma above,
parameterized by evaluated nonsingularity.

## Consequence

Once these two lemmas are supplied, S1329ConcreteCriterion follows:

- forward: l • P = 0 -> class(smulEval)=0 -> smulEval 2 = evalDivisionPolynomial = 0;
- backward: evalDivisionPolynomial=0 -> smulEval 2=0 -> class=0 -> l • P=0.

Then torsion cardinality/root count can proceed via S1362/S1379.

## Conclusion

- actual: S1626 zsmul point formula and ringEval map.
- exact first missing: evaluated nonsingularity of s1626SmulEval.
- exact second missing: zero-class criterion class(smulEval)=0 <-> third=0.
- no Lean file: any file would only assume these fields; no fake.
- report only, EXIT=0.
