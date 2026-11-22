# S2022: the quotient stack [Z / mu_l] -- torsor-stack package and exact first missing

File: tmp/sheaf/xif/paper/S2022QuotientStackActual.lean
SHA-256 (lean): 5820AA47387C0539CD066FD7A216CAA092B069223D5B1650A1BD2589F33A5A1C
EXIT: 0  (lean, no warnings, no sorry/admit/new axiom; 894 lines)
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S2022QuotientStackActual.olean
SHA-256 (olean): 4F18EF884AF7E88FC421F423B57A8138FD8AF972D08150691369D1533BBD0C50
Consumer check: _S2022Consumer.lean EXIT=0 (imports the olean; examples and #check pass).
Axioms: every #print axioms block is contained in {propext, Classical.choice, Quot.sound}.
No IsStack instance, axiom, sorry or fabricated stack/equivalence is used.

## What the file constructs (unconditional, pointwise)

§1  S2022Mu R l: the group of l-th roots of unity in a commutative ring as
    {u in R^x | u^l = 1} (a Subgroup of R^x, with the Group instance), plus
    functoriality S2022Mu.map.
    S2022Zc R l = {b : R | b^l = 0}: the thickened origin Z = Spec K[t]/t^l, the
    action zeta . b = zeta * b with its laws, and the action groupoid S2022Zhom
    (morphisms zeta with y = zeta * x), proved to be a groupoid (S2022ZhomGroupoid).

§2  The action groupoid is the S1997 root fibre: S2022zhEquiv (hom bijection),
    S2022toRoot / S2022ofRoot and the equivalence S2022ZEquivRoot.
    This is the pointwise action-groupoid presentation of [Z / mu_l].

§3  Principal homogeneous spaces S2022PHS (nonempty, free and transitive mu_l-set),
    * S2022PHS.trivialize: every pointwise torsor is trivial (P = mu_l);
    * the trivial torsor S2022PHS.trivial;
    * the associated twist S2022PHS.twist = (P x Z)/mu_l (a Quot, not a placeholder),
      S2022PHS.twistToZ / twistOfZ / twistEquiv: the twist is Z;
    * the torsor/twist dictionary S2022PHS.twistEquivariantEquiv:
      {equivariant maps P -> Z} = points of the twist (item (ii) of S2002 §5).

§4  (iv) the comparison at the pointwise level, fully proved:
    * objects: S2022PhiEquiv  Z(R) = {equivariant maps from the trivial torsor to Z};
    * morphisms: S2022PhiTwistHomEquiv   {c | c . y = x} = S1997RootHom x y
      (the comparison sends a root morphism zeta to the right translation by zeta^-1);
    * origin: S2022PhiTwistHomZero (the stabilizer at 0 is all of mu_l) and
      S2022RootHomZeroEquiv (End(0) = mu_l), matching S1997CyclicOriginAut.

## The package and the reductions

§5  S2022QuotientStackPackage K l: (Q, Q.IsStack, comparison : rootPrestack -> Q,
    fullyFaithful at every test object), i.e. S2002 §5's items (i)+(iii) together with
    the comparison data whose pointwise content §4 proves.
    * S2022QuotientStackPackage.faithfulAtOrigin: faithfulness at the origin is DERIVED
      from full faithfulness (it is not a field of the package).
    * toRootStackification: the package gives S1997's root stackification;
      toRootStackificationMissing, toS2002Datum, toCorrectedDatum (S2019), toS1994.
    * stacky_point: any package has a nontrivial order-l automorphism.
    * not_discreteFiber: no package is realised by a discrete-fibre (in particular
      representable) stack -- S2002's no-go, so the package is not satisfiable
      by the trivial/terminal stack.
    * prestack_realization / of_prestack / prestack_iff_S2019FirstMissing:
      the package is realised by the root prestack itself iff the root prestack is a
      stack, i.e. iff S2019FirstMissing.  So the quotient-stack route is exactly the
      prestack route plus the possibility of a genuinely larger quotient stack.

§6  S2022FirstMissing K l = Nonempty (S2022QuotientStackPackage K l): the exact first
    missing, with the consumer chain
      S2022FirstMissing -> S1997RootStackificationMissing (and S2002's datum,
      S2019's corrected datum, S1994StackyOrbicurveMissing), and
      S2019FirstMissing -> S2022FirstMissing (the old route is the prestack case).

## Exact first missing (not proved, no inhabitant asserted)

The missing is S2002 §5's items (i)+(iii): the etale-local quotient stack [Z/mu_l] as a
genuine stack, i.e. the stack of etale-locally trivial mu_l-torsors and effectivity of
descent for it (Giraud/stackification).  Items (ii) (twist, §3) and (iv) (comparison,
§4) are constructed here.  The missing is NOT the effectivity of descent for the root
prestack: prestack_iff_S2019FirstMissing identifies the prestack realisation exactly
with S2019FirstMissing, and S2002/S2019 record that the Kummer effective-descent failure
is expected there.  No IsStack instance is asserted anywhere.

## Honest boundary

The pointwise model does not satisfy the package: pointwise every torsor is trivial, so
the comparison is an equivalence; what is missing is precisely etale-local triviality
being non-global.  The file does not claim that the package implies or refutes
S1997RootEffectiveDescent; it proves only that no theorem of the file uses it and that the
prestack realisation is equivalent to it.  Shared coordination files (STATE/queue/
AUDIT_LEDGER) were not edited by this package; the parent should update them.
