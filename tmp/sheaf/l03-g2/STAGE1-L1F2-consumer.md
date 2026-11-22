# STAGE 1 consumer record — L1-F2 curve pre-Galois G2

Status: phase-1 statements/scope only. No production proof written. No claim of an inhabitant.

Sources read:
- coord/LAYER1-PLAN.md
- coord/STATE.md
- coord/queue.md
- LeanFormal/IUT/IUTII/Frobenioid/Example36CurveGaloisCategory.lean
- existing tmp/sheaf/l03-g2/STAGE1-source-scope.md

## 1. Exact L1-F2 target object and field

The frozen structure is

    structure CurvePreGaloisCategoryRemainingFields (S : Scheme.{u}) where
      hasQuotientsByFiniteGroups :
        forall (G : Type u) [Group G] [Finite G],
          Limits.HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)

For the actual source curve:

    curveAffinePreGaloisRemainingFields K :
      CurvePreGaloisCategoryRemainingFields (curveScheme K)

The once-punctured source is definitionally the affine curve scheme:

    curveOncePuncturedScheme K = curveScheme K

so the once-punctured source share the same remaining field. The two-punctured
object curveTwoPuncturedScheme K is the extra curve E \ {O,P}, not the source,
and has a separate remaining-field abbrev.

Thus the exact L1-F2 G2 statement is the scheme-cover statement

    forall (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))

and not a statement about the stack-valued OrbicurveFiniteEtaleCover category.

## 2. Actual consumers and relation to L0.3 source G2

Direct consumer in the current repository:

- Example36CurveGaloisCategory.CurvePreGaloisCategoryRemainingFields and its
  curveAffinePreGaloisRemainingFields / realized abbreviations.
- The docstring explicitly records this card as remaining data: no inhabitant is
  constructed in Example36CurveGaloisCategory and no theorem consumes it there.

Layer-1 consumer relation:

- LAYER1-PLAN lists the actual consumers as SourceOrbifurveGroupData /
  OrbicurveEtaleFundamentalGroup (via the curve pre-Galois layer).
- However, the direct L1-F2 field is scheme-level. The source consumer
  OrbicurveEtaleFundamentalGroup uses OrbicurveFiniteEtaleCover X, whose objects
  are category-valued etale stacks with representable finite-etale maps, not
  scheme FiniteEtaleCover S.
- Therefore L1-F2 scheme G2 is necessary but not by itself sufficient for the
  actual source Galois category. The S1 comparison and S2 transport record are
  still required:
  S1: a comparison equivalence FiniteEtaleCover S to OrbicurveFiniteEtaleCover X;
  S2: transport HasColimitsOfShape along the equivalence using E.inv.
- The once-punctured source uses curveScheme K and shares L1-F2 directly; the
  sign-quotient orbicurve and two-punctured extra curve do not follow by a name
  or signature equality.

## 3. Donors and current gap

Donor status checked from the current sources:

- AffineBaseFiniteEtaleQuotients.lean builds section finiteness/etaleness and
  quotientCoverOfDiagram for a single-object action diagram.
- AffineQuotientCoconeIsColimit.lean contains quotientCover but explicitly says
  the cocone IsColimit proof is not included: only affine-target universal
  property is available, not the cover-level universal property.
- AffineQuotientUniversalProperty.lean provides the affine-target algebraic /
  Spec-level factorisation, not HasColimitsOfShape for FiniteEtaleCover.
- GlobalQuotientUniversalProperty.GlobalQuotientCoconeResidual S is exactly the
  unproved scheme-side Prop.

Current exact gap:
No green theorem currently inhabits

    forall (G) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K)).

Consequently CurvePreGaloisCategoryRemainingFields (curveScheme K) has no
actual inhabitant in the current sources. Filling it from a hypothesis or a
data card would be substitution, not proof.

## 4. Minimal freezeable consumer target

Local target L1-F2a (scheme G2 for the actual source curve):

    theorem curveScheme_hasQuotientsByFiniteGroups
      (K : Type u) [Field K] :
      forall (G : Type u) [Group G] [Finite G],
        HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))

This is the theorem needed to construct

    noncomputable def curveAffinePreGaloisRemainingFieldsActual
      (K : Type u) [Field K] :
      CurvePreGaloisCategoryRemainingFields (curveScheme K) :=
      { hasQuotientsByFiniteGroups := curveScheme_hasQuotientsByFiniteGroups K }

Once L1-F2a is green, the once-punctured source field follows by the
definitional equality curveOncePuncturedScheme K = curveScheme K. The
two-punctured extra object needs its own theorem for curveTwoPuncturedScheme K.

For the actual L0.3 stack-valued source, the separate chain remains:

    L1-F2a + S1 comparison equivalence -> S2 transport
      -> HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X).

## 5. Proof-stage boundary

- statement_compiles: L1-F2a can be stated directly against the frozen
  structure; no new object or field is needed.
- proof_body_checked: not yet; the donor IsColimit/HasColimits proof is missing.
- kernel_closed: not yet.
- target_accepted: not yet.

No production Lean file was modified in this phase-1 task.
