# C9 no-sorry report: C9QNormFactorUnconditional

Task: task-478. Owner: kummer. Date: 2026-10-25.
Report only; no Lean/Project edits outside the named MD; no mixed/E3.
Only this file written. target_accepted=false; P6 open.

## 0. Target and verification

Target Lean file:

    tmp/sheaf/n8/closure/C9QNormFactorUnconditional.lean

- 82 lines, 3204 bytes.
- SHA256 05a469bddcdbddf6810f435506e13a62e6328b577ada90f57e4cd3587181e656.
- Compiled with:

      pwsh -NoProfile -File D:\lean\tmp\n8-20261018\lead\lean-serial.ps1         env lean -R D:/lean -j1 tmp/sheaf/n8/closure/C9QNormFactorUnconditional.lean

  Result: EXIT 0.
- Olean:

      D:\lean\.lake\build\lib\lean\tmp\sheaf\n8\closure\C9QNormFactorUnconditional.olean
      16672 bytes,
      SHA256 092fd6efd36d62c3f25efd2ad6cf21d171e5d7051f4545c32765258016bb6e41.

## 1. Sorry/axiom audit

A source text search for sorry/axiom/admit in the target returns only four
**comment** occurrences:

- line 12: "zero-sorry packaging";
- line 29: "No axiom and no sorry is introduced";
- line 30: "sorry is introduced";
- line 67: "zero-sorry conditional packaging".

There is **no actual Lean sorry, admit, or axiom declaration** in the target.
Therefore there is no provable sorry to replace in this file.

No fake declaration, axiom, toy field, or placeholder was introduced.

## 2. What the target actually proves

The file gives the strongest zero-sorry conditional packaging:

1. It defines the exact missing proposition

       MissingNormalizedSpectralFormula S := NormalizedCanonicalQComparison S.

2. It proves the equivalence

       missingFormula_iff_qNormFactor :
         MissingNormalizedSpectralFormula S <-> QNormFactor S.

3. It proves the conditional implication

       qNormFactor_of_missingNormalizedSpectralFormula :
         MissingNormalizedSpectralFormula S -> QNormFactor S.

4. It defines the unconditional target as QNormFactor S and proves

       unconditionalTarget_iff_missingFormula :
         UnconditionalQNormFactorTarget S <-> MissingNormalizedSpectralFormula S.

These are real proved theorems in the target; none is a sorry/axiom.

## 3. Exact obstruction

The unconditional E15 factor

    localSignedLog(qCandidate S) = d S * Real.log ||qUnit S||

is not proved because the following declaration is missing:

    NormalizedCanonicalQComparison S :
      normalizedQLog S =
        -((qCandidate S).exponent : Real) * log(absNorm (pF S)) / d S.

Equivalently, it is the normalized spectral norm formula at the q candidate.

The target file also records the attempted repair obstruction:

- LeanFormal/IUT/Foundations/AlgebraicGeometry/BaseScalarValuationRelation.lean
  does not compile with the current tree. Observed errors include:
  * line 39: PadicScalarField place : Type vs Type u universe mismatch;
  * line 46: deterministic isDefEq heartbeat timeout;
  * line 49: Fact (Nat.Prime (pNat place)) instance mismatch;
  * line 59: Rat.padicValuation_self simplifier shape mismatch;
  * downstream errors in valuation_completionMap, PadicInt.mkUnits,
    zpow_eq_one_iff_right and field_simp API shapes.
- GeneralNormalizedNormFormula.lean and
  GeneralNormalizedNormBySpectralUniqueness.lean have no oleans and their
  sources fail under the current API (Valued instance/Real.log_zpow errors).
- Repairing those modules is a source-module change outside this file's scope;
  it cannot be replaced by an axiom, sorry, or toy hypothesis.

The exact leading missing bridge is therefore the normalized spectral
comparison declaration above, implemented through a working
BaseScalarValuationRelation / GeneralNormalizedNormFormula chain.

## 4. What was and was not changed

Changed:

- this report file only.

Not changed:

- no Lean source edit;
- no import edit;
- no axiom/sorry/toy inserted;
- no other project file touched.

Since the target contains no actual sorries, "replace only provable sorries"
has empty replacement set. The existing conditional packaging already
discharges every implication the file can prove from available declarations.

## 5. Compile status

- Target statement compiles: YES, EXIT 0 via lean-serial -j1 -R D:/lean.
- Actual sorries in target: NONE.
- Axioms in target: NONE.
- Unconditional target theorem: NOT proved; conditional on
  NormalizedCanonicalQComparison S.
- The missing source/API repair: EXACT OBSTRUCTION recorded in Section 3.

## 6. Classification

| item | status |
|---|---|
| target Lean file compiles | YES, EXIT 0 |
| actual sorry in target | NONE |
| actual axiom in target | NONE |
| fake/toy placeholder | NONE |
| missingFormula_iff_qNormFactor | PROVED |
| qNormFactor_of_missingNormalizedSpectralFormula | PROVED conditional |
| unconditionalTarget_iff_missingFormula | PROVED equivalence |
| NormalizedCanonicalQComparison S | MISSING |
| BaseScalarValuationRelation.lean current compile | BROKEN |
| GeneralNormalizedNormFormula.lean | NO OLEAN / API FAIL |
| GeneralNormalizedNormBySpectralUniqueness.lean | NO OLEAN / API FAIL |
| unconditional QNormFactor | NOT PROVED |

## 7. Conclusion

The target C9QNormFactorUnconditional.lean is already a no-sorry,
no-axiom, compiling file. It proves the exact equivalence between the
unconditional QNormFactor target and the missing normalized spectral formula,
plus the conditional implication. The unconditional factor is not proved
because NormalizedCanonicalQComparison S is missing; the attempted repair is
blocked by non-compiling source/API modules BaseScalarValuationRelation,
GeneralNormalizedNormFormula and GeneralNormalizedNormBySpectralUniqueness,
which are outside this file's scope. No fake declaration or toy replacement was
used. The exact obstruction is documented; the target remains conditional.

No Lean edits; no mixed/E3; target_accepted=false; P6 open.

## 8. Status

- No-sorry/no-axiom audit and compile verification only; no Lean edits.
- Target compiles EXIT 0; actual sorries none; exact missing declaration
  NormalizedCanonicalQComparison S recorded.
- target_accepted=false.
