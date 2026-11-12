# S2834 — 10-input audit: automatic derivability

Date: 2026-11-07. Target: `S2834CompletionAutoTorsionActual` uses 10 explicit
inputs. This audit classifies which are automatic, which are supplied by an
existing actual, and which are genuine blockers.

**MAJOR CORRECTION (2026-11-07):** this audit is for the intermediate
`S2786Arithmetic` (K = Q(i)) version only. `S2786Arithmetic` is NOT valid for
ClauseC. `arithmetic37` is ALSO invalid for ClauseC: its F = Q(i) and E[6] is
not rational there. The correct A6 is F = F6 = S2790F6, curve =
S2790E.baseChange F6, K = kernel field over F6. S2834 and this audit must not
be cited as the final T; qside is rebuilding on F6 in S2847.

## 1. The 10 inputs

1. `S : SourceSignQuotientData S2786Arithmetic`
2. `hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad`
3. `hreal : uniformization` on `V_mod_bad` places
4. `torsion23Rational : S2786Arithmetic.curve.Torsion23Rational`
5. `imageContainsSL2 : SL2 <= galois representation range`
6. `kernelFieldIdentification : K ≃ₐ[F] kernelField`
7. `kernelFieldIdentificationRange : Set.range ... = kernelField`
8. `kSide : S2817ClauseDScaffold`
9. `localFamily : SourceClauseELocalFamilyUnit ...`
10. `boundary : SourceClauseFBoundaryUnit ...`

## 2. Audit

### Automatic / reduced

- **hV (input 2): conditionally automatic.** Actual lemma
  `S2834InputAuditActual.S2834_hV_of_VmodBad` (olean 10232 B,
  SHA 8FF7B78BF6CD0225B2001D579405127811D2A70AEBE796C01414BC23A256670B;
  axioms trio) reduces hV to `S.V_mod_bad = S2786VmodBad`, using the actual
  `S2786PlaceSelection_V_mod_bad : S2786PlaceSelection.V_mod_bad = S2786VmodBad`.
  So hV is rfl **once an S is built with `V_mod_bad := S2786VmodBad`**. For an
  arbitrary S it is not automatic.
- **kernelFieldIdentification / range (inputs 6-7): NOT automatic for
  `S2786Arithmetic`.** `S2834KernelFieldIdentificationActual` is ACTUAL
  (olean 31968 B, SHA B8CE8D93...; axioms trio), but it is the identity
  `AlgEquiv.refl` for `arithmetic37`, whose `K` is definitionally `K37`.
  `S2786Arithmetic.K` is `GaussianField`, while `K37` is an
  `IntermediateField GaussianField (AlgebraicClosure GaussianField)`; they are
  not definitionally equal. To derive the S2834 input one must first prove
  `K37 = ⊤` (all 5-torsion is rational over Q(i), which S2771's basis suggests)
  and then use the top-field equivalence; that proof is missing. Range follows
  from the equivalence but is not rfl.

### Missing / no supplier

- **S (input 1): MISSING.** `S2786SignQuotientActual` supplies the place block
  `S2786PlaceFields : S2490AllPlacesFields S2786Arithmetic`, not a full
  `SourceSignQuotientData`. No constructor for the 30-field sign-quotient data
  exists in the current tree. This blocks inputs 1, 8, 9, 10.
- **hreal (input 3): MISSING supplier.** No theorem supplies
  `CurveIndexedTateUniformization` for all `V_mod_bad` places; it is an input.
- **torsion23Rational (input 4): MISSING.** S2790 has the F6 definition but the
  `Torsion23Rational` instance is not supplied (GAPS G8).
- **imageContainsSL2 (input 5): NOT automatic.** S2783 is conditional on
  `S2783QuadraticBaseChangeData` including the SL2 perfectness and quadratic
  restriction inputs; S1298's large-image field is also conditional. No actual
  unconditional `imageContainsSL2` for this curve/basis.
- **kSide (input 8): MISSING.** `S2817ClauseDScaffold` is a 14-field structure
  (`kSignAction`, `kQuotient`, `kQuotientWitness`, extensions, groups, exact
  sequences). S2817 supplies only the constructor `S2817ClauseD` from the
  scaffold; no inhabitant is constructed.
- **localFamily (input 9): MISSING.** `SourceClauseELocalFamilyUnit` is
  consumed through `S2817ClauseEScaffold` (finite/infinite local sources); no
  supplier is constructed.
- **boundary (input 10): MISSING.** `SourceClauseFBoundaryUnit` is consumed by
  the ClauseF scaffold; no concrete boundary unit is constructed.

## 3. Bottom line

Automatic after choosing canonical S: only **hV**, and only under
`S.V_mod_bad := S2786VmodBad`.

Everything else is either a genuine input (hreal, torsion23Rational,
imageContainsSL2) or blocked by the missing canonical S and K-side/local/boundary
constructors (kSide, localFamily, boundary), plus the non-rfl kernel-field
comparison.

## 4. Next executable steps

1. Prove `K37 = ⊤` from the S2771 full torsion basis and derive
   `kernelFieldIdentification` via `IntermediateField.topEquiv`; this closes
   inputs 6-7 for the canonical arithmetic.
2. Construct a canonical `SourceSignQuotientData` with
   `V_mod_bad := S2786VmodBad`; hV then follows by the actual reduction lemma.
3. Then attack kSide/localFamily/boundary constructors; these are the larger
   missing objects.
