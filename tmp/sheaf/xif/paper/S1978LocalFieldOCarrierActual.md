# S1978: the actual local-field O^× carrier on the S1895 input

Date: 2026-11-01 (Asia/Shanghai).  File:
tmp/sheaf/xif/paper/S1978LocalFieldOCarrierActual.lean.

## Verdict

**Constructed (EXIT=0, kernel-checked)** for the actual local O^× carrier and its
attachment to the S1895 boundary/strip slots and to a reduced paper q-pilot
object.  **Missing** for the input-level rebasing and the paper's group-theoretic
actor; the exact missing types are recorded without inhabitants.

## What S1967 left

S1967 proved that the S1895 input is built on the S1487 shear strip, whose value
monoid is SourceHaarActualValueMonoid (the additive monoid of nonpositive
reals), so its unit group is trivial.  The reduced kappa^{x mu} representatives
on that carrier are identity completions in content, and cannot be identified
with a genuinely nontrivial local-field O^×μ.  S1967 constructed a local model
LocalOUnits p = (AlgebraicClosure Q_p)^x but did not attach any local unit
carrier to the S1895 place type.

## Constructed (checked)

* **Actual local O^× carrier.**
  LocalOFieldUnits p = (Integers (AlgebraicClosure Q_p))^x, the actual integral
  unit group of the actual algebraic closure, at every place v of the S1895
  one-column via p = v.1.
* **Actual local Galois action.**
  LocalOFieldUnitsAction p is the actual action of LocalAbsoluteGalois p by
  localGaloisUnitMap; LocalOFieldUnitsMu p = TimesMuQuotient (O^×) carries the
  descended action.
* **Genuine nontriviality.**  localOFieldUnit p is the concrete integral unit
  1 + p.  localOFieldUnit_not_isOfFinOrder proves it is not a root of unity
  (otherwise injectivity of Q -> AlgebraicClosure would force (1+p)^n = 1 in Q,
  impossible since 1 < 1+p).  Hence localOFieldUnit_quotient_ne_one and
  LocalOFieldUnitsMu_nontrivial: the actual O^×μ quotient is nontrivial at every
  prime.
* **Actual F-prime-strip.**  localOFieldStrip : FPrimeStrip (FinitePrimePlace
  2 7) has value monoid the actual O^× group at v.1, Pi/G the actual local
  absolute Galois groups, actual local Galois action, and actual norm-log
  degree.  localOFieldStrip_unitsAction_groupUnitsEquiv identifies the strip's
  units action with the actual O^× action.
* **Canonical kappa-orbit datum.**  localOFieldKappaDatum is the canonical
  KappaOrbitUnitsActionDatum of IUT II, Definition 4.9, on the actual local
  O^× strip over the product of local Galois groups; its source module is the
  actual O^× group up to the canonical group-units equivalence, and
  localOFieldKappaDatum_sourceAction_equiv proves the source action is the
  actual local Galois action.
* **Boundary/strip attachment.**  localOFieldTheater, localOFieldBoundary and
  localOFieldBoundaryStrip put the actual local O^× strip into the
  OrigXiFPaperBoundaryStripFields package used by S1895PaperO, keeping the S1895
  input, one-column carrier, scalar and route-normal-form data.  Strip anchors
  and the (1,0) label are proved.
* **Reduced paper q-pilot object.**  localOFieldPaperO is a PaperQPilotObject on
  the S1895 input whose strip is the actual local O^× strip.  Its strip
  anchors, (1,0) label, local F-times-mu slot, local log-Kummer slot, actual
  S1679 line-bundle slot and actual q-pilot scalar slot are all proved.  The
  two strip/Kummer slots are explicitly local analogues, not the paper's
  identifications.
* **No identification with the degenerate carrier.**
  no_localOFieldUnits_equiv_sourceHaarUnits, no_localOFieldStrip_equiv_shear,
  no_localOFieldStrip_equiv_paperO, paperO_strip_ne_local and
  paperInput_core_ne_local prove that the actual local O^× strip cannot be
  identified with the S1487 value monoid or with (S1895PaperO D).strip.
  S1978FirstMissingBridge_impossible proves the corresponding full times-mu
  bridge is uninhabited.

## Exact first missing

* S1978RebasedPaperInput D: an OriginalInput with the same initial data as the
  S1895 input whose (1,0) F-prime-strip is localOFieldStrip.  This is the
  input-level replacement of the degenerate value monoid.
* S1978RebasedPaperO D: the corresponding PaperQPilotObject with that strip.
* S1978FirstMissing D := S1978RebasedPaperO D.

No inhabitant is asserted.  The S1527 family/boundary must be rebuilt with the
actual local strips, and the paper's group-theoretic actor
G |-> O^×(G), G |-> O^×μ(G) of IUT II, Example 1.8, (iii), (iv), together with
the factorization through the local Galois groups, remains missing.

## Scope

At a place v the carrier is the local model at the rational prime v.1 (the
Q_p-model used by S1967's LocalOUnits p and by the local-integral
F-prime-strip), not the completion of the number field at QPlace v.  It is the
actual integral unit group of the actual algebraic closure of Q_p with the
actual local Galois action.  The completion-level carrier of S1949 and this
Q_p-model are different actual carriers; no equivalence between them is
asserted here.

## Evidence

* source file: tmp/sheaf/xif/paper/S1978LocalFieldOCarrierActual.lean, 757
  lines, SHA256 16E77B49A4577635C8E83488938C0E1A6F689819D6E3D56717D528BD455364CD
* compile: lake env lean -j1 -R D:\lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1978LocalFieldOCarrierActual.olean
  tmp/sheaf/xif/paper/S1978LocalFieldOCarrierActual.lean
  EXIT=0; S1978.compile.log contains only the #print axioms output, no
  warnings or errors.
* olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1978LocalFieldOCarrierActual.olean,
  552320 bytes, SHA256 CF2B3E1F609CA601F84DA6D7D556E4B5719CD7097BCA246812B8674A69A84587.
* axioms: every probed declaration depends only on [propext, Classical.choice,
  Quot.sound]; no sorryAx.
* forbidden tokens: no sorry/admit/axiom/unsafe/native_decide/partial in the
  file (the only occurrence of the word axiom is in the docstring and the
  #print axioms commands).
* consumer: tmp/sheaf/xif/paper/_S1978Consumer.lean, EXIT=0, imports the final
  olean and checks the nontriviality, the strip monoid, the no-go and the
  boundary/paper object projections.

## Not run

Full Project build, target comparator, independent review.
