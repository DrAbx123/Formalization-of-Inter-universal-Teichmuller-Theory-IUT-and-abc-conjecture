# S1906: actual rank-two l-torsion of E'/F' via division polynomials

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1906RankTwoTorsionActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1906RankTwoTorsionActual.olean

## Verification

- Build command: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1906RankTwoTorsionActual.olean tmp/sheaf/xif/paper/S1906RankTwoTorsionActual.lean
- EXIT=0, 0 errors, 0 warnings.
- Source SHA256: 8D6D17A10439F50789C0FE7DEEFFEAD04546007FF4CA75C73835ECDF6EFCF161
- Source bytes: 34206
- Olean SHA256: CEF39ADAADA1C699B3C40671153D69DFA227DDCBC86ABDB849AEE6AD8E31F501
- Olean bytes: 395656
- Olean import re-check: EXIT=0 (a scratch module imports the olean and #checks four main declarations).
- All #print axioms report only [propext, Classical.choice, Quot.sound]; no sorryAx, no axiom declaration, no opaque/placeholder.

## What is proved unconditionally

1. S1906RankTwoBasisGap_iff_natCard:
   S1725RankTwoBasisGap l <-> Nat.card (S1720Curve.LTorsion l) = l.value ^ 2.
   No finiteness hypothesis (infinite types have Nat.card = 0).
2. S1906RankTwoBasisGap_iff_finrank:
   S1725RankTwoBasisGap l <-> Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) = 2.
   No finiteness hypothesis (infinite modules have finrank 0).
3. S1906FiniteFreeRankTwo_of_basisGap / S1906FiniteFreeRankTwo_of_natCard:
   a basis (or just the cardinality l^2) gives Module.Finite / Module.Free /
   finrank = 2 for the actual E'[l].
4. S1906NatCard_le_sq_of_detection and S1906Finite_of_detection:
   the missing forward detection l • P = 0 -> psi_l(P) = 0 alone gives
   |E'[l]| <= l^2 and finiteness (via the explicit l-division candidate locus
   and WeierstrassCurve.card_le_of_prime_divisionLocus_with_zero).
5. S1906Criterion_iff: the group-law criterion is exactly
   S1906Detection l and S1906ZeroCriterion l.
6. S1906NatCard_eq: under the criterion,
   Nat.card E'[l] = 1 + 2 * #(distinct roots of prePsi_l).
7. S1906NatCard_eq_sq_iff_rootCount and
   S1906RankTwoBasisGap_iff_rootCount_of_criterion:
   under the criterion, the basis gap is exactly the full root count
   #roots = (l^2 - 1) / 2.
8. S1906RootCount_of_separable: separability of prePsi_l gives the root count.
   S1906RootCount_of_genericPreΨSeparable: the tree input
   S1366GenericOddPreΨSeparableInput gives the root count.
9. S1906BasisGap_of_xCoordinateFormula_zeroCriterion_genericSeparable:
   the missing x-coordinate formula + S1906ZeroCriterion + the S1366 generic
   separability input imply S1725RankTwoBasisGap l (and hence the D5 basis).
10. S1906ExactFirstMissing (Nat.card E'[l] = l^2) is equivalent to
    S1725RankTwoBasisGap l (S1906ExactFirstMissing_iff_basisGap).

## Exact first missing

Target-level exact first missing (equivalent to the basis gap, no hidden data):

  Nat.card (S1720Curve.LTorsion l) = l.value ^ 2.

The standard division-polynomial proof decomposes this into the following
three explicit classical/algebraic inputs, all recorded as hypotheses:

(a) s1361XCoordinateFormula S1906W (l.value : Z):
    x([n]P) = Phi_n(P) / psi_n(P)^2 for n >= 4.  Mathlib v4.32.2 has no such
    lemma for n >= 4 (the bivariate omega_n is an explicit TODO in Mathlib);
    S1361 proves the n = 1, 2 cases and reduces detection to this formula.
(b) S1906ZeroCriterion l = s1361ZeroCriterion S1906W l:
    psi_l(P) = 0 -> l • P = 0.  Mathlib has no reverse detection for l >= 3.
(c) S1906Separability l = (S1906W.preΨ (l.value : Z)).Separable.
    This is the characteristic-zero odd part of TauCeti's separable_prePsi;
    it is exactly the tree input S1366GenericOddPreΨSeparableInput (S1366) and
    the exact first algebraic lemma of the derivative route S1420.  TauCeti is
    Lean v4.36.0-rc1 / newer Mathlib and is not importable at this pin.

No fake basis, no new axiom, no True-valued placeholder.  The basis is only
produced from a genuine cardinality equality or from the three named inputs.

## Consumers

- S1894D5LargeImageActual: uses S1725RankTwoBasisGap as the rank-two input.
- S1725SourceTorsionFPrimeActual: S1725RankTwoBasisGap is the rank-two basis gap.
- SourceTorsionCarrierReduction.RankTwoTorsionBasisGap: equivalent frozen card.

## Note on the environment

The shared checkout had intermittent "failed to read file ... .olean" errors
from concurrent Lean builds.  The final build and import test were rerun until
EXIT=0; the reported hashes are the successful artifacts.
