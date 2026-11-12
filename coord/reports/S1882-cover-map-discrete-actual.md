# S1882: S1766CoverMapDiscrete and the doubled / terminal cover 2-iso classes

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1882CoverMapDiscreteActual.lean

EXIT=0

SHA256 (source): BB2FDA16A24C6D068599B40843124CA9C1CD50413D9D5F31937EB8DD238EBF29

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1882CoverMapDiscreteActual.olean
(289840 bytes, SHA256
BD48E0077EAD68224B4241F69A49123E3C2DF9E852B970818566943934400F64)

## Question

S1766 isolated the exact residual of raw R2a:

  S1766CoverMapDiscrete :
    forall (A B : S1728Cover) (f g : S1728CoverMap A B),
      S1728CoverMapRel f g -> f = g

and S1809 proved that it is exactly the missing input for the raw small cover
data S1728SmallRawCoverDataRequired.  S1850 constructed the doubled cover
S1850DoubledCover, whose identity-point presentation is the doubled square but
whose source and map are the same as the terminal cover; its identity-point
self-endomorphism is fold ; inl, not the identity.  Task: prove or refute
S1766CoverMapDiscrete using the doubled/terminal 2-iso classes, and record raw
small data feasibility, or identify the exact first missing.

## Result: the doubled cover does not refute; target-local discreteness is proved

The new unconditional lemma is:

  S1882StrongTrans_eq_of_modification
    {W : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    {eta theta : StrongTrans W (S1742YS S)}
    (e : eta ⟶ theta) : eta = theta

i.e. any modification between strong transformations into a representable
etale stack forces equality of the strong transformations.  The proof uses the
new instance S1882CatHom₂Subsingleton (2-cells into a discrete category are
subsingletons, with no hypothesis on the source), the functor equality
S1882Functor_eq_of_natTrans_discrete, and the S1790/S1761 style strong
transformation extensionality.

Consequences:

* S1882StrongTrans_iso_iff: for a representable target, 2-isomorphic strong
  transformations are equal.

* S1882CoverMapDiscrete_of_targetEq: if B.source.fiber = S1742YS S, then any
  two 2-isomorphic cover maps A -> B are equal.

* S1882DoubledCover_sourceRepresentable and
  S1882TerminalCover_sourceRepresentable: both covers have source fiber
  S1742YS S1726AffineOver (rfl).

* S1882DoubledCover_targetDiscrete, S1882TerminalCover_targetDiscrete, and
  the explicit forms S1882DoubledCover_discrete / S1882TerminalCover_discrete.

* S1882DoubledCover_rel_iff and S1882TerminalCover_rel_iff: at these targets
  the 2-isomorphism relation is literally equality; there is no non-trivial
  2-iso class.

* S1882DoubledCover_structure: the doubled cover is source-representable AND
  its S1756End is not the identity.  Hence the failure of the unit 2-cell is
  not a 2-isomorphism between two distinct cover maps.

## Raw small cover data

* S1882QuotEquivRawOfTargetDiscrete: under target-local discreteness, the
  2-isomorphism quotient is equivalent to the raw cover maps.

* S1882RawSmallDataOfTargetDiscrete: the Type-0 carrier S1766QuotSmallCarrier
  is equivalent to the raw maps.

* S1882RawSmallDataTerminal / S1882RawSmallDataDoubled: for every A, raw
  small cover data into the terminal/doubled target is unconditionally
  inhabited (Type-0 carrier, genuine equivalence).

## Exact residual / first missing

* S1882CoverMapDiscrete_iff_targets:
    S1766CoverMapDiscrete <-> forall B, S1882CoverMapDiscreteAtTarget B.

* S1882FirstMissing is defined as the target-local statement
  (forall B, S1882CoverMapDiscreteAtTarget B), and
  S1882FirstMissing_iff_S1766 proves it equivalent to S1766CoverMapDiscrete.

* S1882AllTargetsSourceRepresentable is the sufficient geometric input
  (every cover source fiber is S1742YS S).  It implies S1766CoverMapDiscrete
  (S1882AllTargetsSourceRepresentable_implies_discrete) and hence, through
  S1809, the raw small cover data
  (S1882RawSmallCoverDataRequired_of_sourceRepresentable).

* S1882Counterexample_target_notSourceRepresentable: every actual counterexample
  to raw R2a must target a cover whose source fiber is not representable.
  S1882NoCounterexampleAtDoubledOrTerminal: neither the terminal nor the
  doubled cover can be the target of a counterexample.

Thus the universal statement is neither proved nor refuted here.  The exact
residual is target-local discreteness for a target whose source is not the
representable stack of a scheme; the present file constructs no such target.
The generic pullback and coherence constructions (S1864, S1871, S1891) leave
their non-representable-source covers conditional on data and do not supply a
counterexample.

## Honest boundary

No sorry, no admit, no new axiom, no Shrink/ULift/PUnit, and no fake data.
Every #print axioms in the file reports only propext, Classical.choice and
Quot.sound.  The universal S1766CoverMapDiscrete (and hence
S1728SmallRawCoverDataRequired) is not asserted; only the target-local
statements above and the conditional implications are proved.

## Evidence

- lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1882CoverMapDiscreteActual.olean
  tmp/sheaf/xif/paper/S1882CoverMapDiscreteActual.lean
  EXIT=0, no warnings, no sorryAx.
- Source 418 lines, 21258 bytes, SHA256 as above.
- Olean 289840 bytes, SHA256 as above.
- Consumer check (separate scratch file, since deleted): importing the module
  and using S1882DoubledCover_discrete, S1882DoubledCover_targetDiscrete and
  S1882RawSmallDataTerminal compiled with EXIT=0.
- All #check and #print axioms blocks at the end of the file pass.

## Next executable step

To prove the universal statement, prove S1882AllTargetsSourceRepresentable
(or the weaker target-local discreteness directly), e.g. by strengthening the
finite-etale base-change datum of every cover source to a strict
representability/retraction.  To refute it, construct a concrete cover whose
source fiber has a nontrivial 2-automorphism (or a target for which
S1882CoverMapDiscreteAtTarget fails); the doubled and terminal covers are
excluded by the results above.
