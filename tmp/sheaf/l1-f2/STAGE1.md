# SHEAF L1-F2 — STAGE 1/2 evidence record

Status: stage 2 statement only. No production file modified.

## S2 green evidence

File: tmp/sheaf/l03-g2/S2Transport.lean
- Build: pwsh -NoProfile -File D:\lean\tmp\n8-20261018\lead\lean-serial.ps1 env lean -j1 tmp/sheaf/l03-g2/S2Transport.lean
- exit 0
- statement_compiles = true
- proof_body_checked = true
- kernel_closed: not separately audited
- no sorry/admit/axiom

Mathematical content: if E : FiniteEtaleCover S.left ⥤ OrbicurveFiniteEtaleCover X
is an equivalence and the scheme side has finite-group action colimits, then the
orbicurve cover category has HasColimitsOfShape (SingleObj G) for every finite G.
Direction: E.inv is used to set C = OrbicurveFiniteEtaleCover X and
D = FiniteEtaleCover S.left; if the target orbicurve category does NOT yet have
the colimits, this theorem gives the scheme side, not the orbicurve side. The
statement is correct only under the scheme-side hypothesis and E : scheme ⥤ orbicurve.

## L1-F2 stage 1 record

Exact frozen target:

    structure CurvePreGaloisCategoryRemainingFields (S : Scheme.{u}) where
      hasQuotientsByFiniteGroups :
        forall (G : Type u) [Group G] [Finite G],
          Limits.HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)

For the actual once-punctured source affine curve:

    curveAffinePreGaloisRemainingFields K :
      CurvePreGaloisCategoryRemainingFields (curveScheme K)

The once-punctured source is definitionally the affine curve
curveOncePuncturedScheme K = curveScheme K. The two-punctured object
curveTwoPuncturedScheme K is the extra curve E \ {O,P}, not the source, and has
a separate remaining-field abbreviation.

Actual consumers:
- Example36CurveGaloisCategory.CurvePreGaloisCategoryRemainingFields,
  curveAffinePreGaloisRemainingFields, and the corresponding realized abbrevs.
- LAYER1-PLAN lists the downstream consumers as SourceOrbicurveGroupData /
  OrbicurveEtaleFundamentalGroup, but those use the stack-valued
  OrbicurveFiniteEtaleCover X category, not the scheme FiniteEtaleCover category.
  Therefore L1-F2 scheme G2 alone does not fill the actual source Galois
  category; the S1 comparison and S2 transport are also required.
- The sign-quotient orbicurve and the two-punctured extra curve cannot be filled
  by name or signature equality.

Current gap:
No green theorem currently inhabits

    forall (G) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K)).

AffineBaseFiniteEtaleQuotients has quotientCoverOfDiagram but no cocone
IsColimit theorem. AffineQuotientCoconeIsColimit explicitly omits the cocone
IsColimit proof. AffineQuotientUniversalProperty is affine-target only.
GlobalQuotientCoconeResidual is exactly the unproved scheme-side Prop.

Minimal consumer target:
L1-F2a: curveScheme_hasQuotientsByFiniteGroups K, directly giving
CurvePreGaloisCategoryRemainingFields (curveScheme K) by
curveAffinePreGaloisRemainingFields_of_schemeG2. For the actual L0.3 stack
source, the chain remains L1-F2a + S1 equivalence -> S2 transport.

## Stage 2 statement file

File: tmp/sheaf/l1-f2/SchemeG2Statement.lean
- statement_compiles = true (lake env lean exit 0)
- proof_body_checked = false (named sorry at the G2 theorem)
- kernel_closed = false
- target: curveScheme_hasQuotientsByFiniteGroups K
- direct entry: curveAffinePreGaloisRemainingFields_of_schemeG2
- once-punctured alias: curveOncePunctured_hasQuotientsByFiniteGroups
- package: curveScheme_hasQuotientsByFiniteGroups_and_remainingFields

No production Lean file was modified.


## S2 axiom probe and L1-F2 consumer evidence (appended)

Probe file: tmp/sheaf/l03-g2/S2Axioms.lean
- Build: pwsh -NoProfile -File D:\lean\tmp\n8-20261018\lead\lean-serial.ps1 env lean -j1 tmp/sheaf/l03-g2/S2Axioms.lean
- exit 0.
- Axioms of the S2 transport theorem (and its direct-hypothesis wrapper):
  [propext, Classical.choice, Quot.sound]
  exactly the allowed set.
- Caveat: the serialized wrapper does not support -o, so S2Transport.olean was
  not produced. S2Axioms.lean therefore contains a verbatim local copy of the
  same S2 statement and proof body for the #print axioms probe. S2Transport.lean
  itself has already been checked exit 0 with no sorry.

L1-F2 consumer evidence in S2Axioms.lean:
- l1f2_curveScheme_hasQuotientsByFiniteGroups_of_kummer:
  given kummer's scheme-level theorem
  (forall G [Group G] [Finite G], HasColimitsOfShape (SingleObj G)
    (FiniteEtaleCover (curveScheme K))),
  the L1-F2 target follows by exact.
- l1f2_curveScheme_remainingFields_of_kummer:
  the same theorem directly constructs
  CurvePreGaloisCategoryRemainingFields (curveScheme K).
- l1f2_consumer_reduction packages both.

Therefore when kummer's HasColimits theorem appears, the named sorry in
tmp/sheaf/l1-f2/SchemeG2Statement.lean can be replaced by exactly that theorem
with no new data, comparison, or hypothesis.
