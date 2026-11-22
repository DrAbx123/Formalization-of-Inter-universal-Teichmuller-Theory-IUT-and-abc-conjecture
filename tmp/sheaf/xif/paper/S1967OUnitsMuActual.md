# S1967: O^×μ domain audit and the operation-level gap

Date: 2026-11-01 (Asia/Shanghai).  File:
tmp/sheaf/xif/paper/S1967OUnitsMuActual.lean.

## Verdict

**Missing** for the paper-level operation-level object.  The file is a checked
audit (EXIT=0), not a construction of the group-theoretic O^×μ(G) or the paper's
κ^×μ/evaluation isomorphism.

The main new finding is a type-level obstruction on the carrier used by
S1951/S1959: the S1895 input is built on the S1487 shear strip, whose value
monoid is SourceHaarActualValueMonoid (the additive monoid of nonpositive
reals).  Its unit group is trivial.  Hence every reduced κ^×μ representative
on that carrier is an identity completion in content, even when it is not
literally TimesMuKummer.Isomorphism.refl.  The actual local-field O^×μ model is
nontrivial, and the two cannot be identified.

## Constructed (checked)

On the available S1895 carrier:

* OUnits v = (LGP.Mon v)^x, OUnitsAction v = the actual action of
  KummerGroup D; OUnitsMu v = TimesMuQuotient (OUnits v) with the descended
  OUnitsMuAction.
* envKappaDatum, gauKappaDatum, lgpLowerKappaDatum : actual inhabitants of
  KappaOrbitUnitsActionDatum, with Kummer representatives induced by the
  actual source links fLinkAt 1 0 0 0, 1 0 0 1, 1 0 1 1.
* envGauPairDatum and operationEvaluationIso: the two-strip form and the
  operation-level evaluation isomorphism env -> gau, factoring through the
  common O^×μ(G) domain.
* operationEvaluationIso_equiv_eq_xMu: its quotient equivalence is the actual
  strip-equivalence transport xMuQuotientEquiv (linkEnvToGau D).
* operationEvaluationIso_equiv_eq_upperEvaluation: it is exactly S1951's
  reduced evaluation unit layer.
* operationSquare_commutes: the operation-level square commutes on the common
  domain.

## No-go on the available carrier (proved)

* sourceHaarActualValueMonoid_units_subsingleton:
  Subsingleton (SourceHaarActualValueMonoid)^x.
* OUnits_subsingleton and OUnitsMu_subsingleton: the reduced O^× and O^×μ
  domains on the S1895 LGP strip are trivial.
* envKappaDatum_kappa_equiv_trivial: the reduced env representative is the
  identity on the quotient.

## Genuine local-field O^×μ(G) model (proved)

* LocalOUnits p = (AlgebraicClosure Q_p)^x;
  LocalOUnitsMu p = TimesMuQuotient (LocalOUnits p);
  LocalOUnitsAction p = localGaloisUnitsAction p;
  LocalOUnitsMuAction p = the descended action.
* localQParameterFor_not_isOfFinOrder: the local q-parameter p is not torsion.
* localQParameterFor_quotient_ne_one and LocalOUnitsMu_nontrivial: the local
  O^×μ quotient is nontrivial.
* no_units_equiv_sourceHaar_local: no multiplicative equivalence between the
  trivial S1487 units and the nontrivial local units.
* no_s1895_units_equiv_local: the same at every S1895 place.
* no_local_to_sourceHaar_timesMuIso: no TimesMuKummer.Isomorphism from the
  local O^×μ module (any action) to the trivial S1487 O^×μ module (any action).

## Exact first missing

(a) The actual local-field O^× carrier on the S1895 source input: replace the
    S1487 SourceHaarActualValueMonoid by the local field units.  Section 9
    proves the present carrier cannot be identified with them.
(b) The group-theoretic algorithm G |-> O^×(G), G |-> O^×μ(G) of IUT II,
    Example 1.8, (iii), (iv), and its identification with the source modules.
(c) The split-Frobenioid identification Aut(‡A) ≅ G_w of IUT II, Definition
    4.9, (ii), with the 2l-torsion and splittings.
(d) The F^⊩ carrier and theta/Gaussian monoids of IUT II, Corollary 4.6,
    (iv), (v), needed for the paper's Corollary 4.10, (ii), evaluation
    isomorphism.  The present evaluation isomorphism is only the reduced
    F^⊢ times-mu unit layer.
(e) The profinite topology; the existing interface uses the indiscrete
    FPrimeStrip.productPiTopology fallback.

## Evidence

* source: tmp/sheaf/xif/paper/S1967OUnitsMuActual.lean, 28745 bytes, 651 lines,
  SHA256 0D1A88BFC8013F927D2548CB3ECCB6DDCF887A0F17B24AE72CD5FCE08AC1DEBC
* compile: lake env lean -j1 -R D:\lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1967OUnitsMuActual.olean
  tmp/sheaf/xif/paper/S1967OUnitsMuActual.lean; EXIT=0; no warnings/errors in
  S1967.compile.log.
* olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1967OUnitsMuActual.olean,
  574136 bytes, SHA256 19C63BFA2EA9666646C2F5BE87D86AB50F104C94168BD1781B397579FD707A27.
* axioms: every probed declaration depends only on
  [propext, Classical.choice, Quot.sound]; no sorryAx.
* forbidden code tokens (sorry/admit/axiom/unsafe/native_decide/partial):
  none.
* consumer: tmp/sheaf/xif/paper/_S1967Consumer.lean, EXIT=0; imports the final
  olean and checks the no-go and evaluation theorems.

## Not run

Full Project build, target comparator, independent review.
