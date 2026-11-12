# S1758: the retraction half of stack representability at the identity point

Layer: D6 orbicurve cover category / S1733 affine finite-etale slice comparison.
Package: S1758, owner: delegated S1758 worker.
Source object: S1743 \`S1743SourceRetraction\`
(\`tmp/sheaf/xif/paper/S1743CoverSliceActual.lean\`).
Reused results: S1743 (identity-point base change presentation, \`S1743Square\`,
\`S1743Lift\`, \`S1743ModelSection\`, \`S1743BaseChange\`), S1733 (\`S1733Model\`,
\`S1733BasePoint\`, \`S1733Slice\`), S1726 (\`S1726AffineOver\`, the orbicurve stack
is the representable stack of \`Spec R'\`), S1742 (not used for the missing
statement; only referenced for why it does not apply).

## Question

S1743 asks: for every actual finite-etale cover \`A\` of the S1726 D6 orbicurve,
is there a strong transformation \`inv : A.source ⟶ Y (S1733Model A)\` with

    vcomp (toSource) (inv)  ≅  id_{Y (S1733Model A)} ?

S1743 proved the opposite composite (\`vcomp (S1743Lift A) toSource ≅ id\`) and
named the missing one \`S1743SourceRetraction\`.

## Result

File: \`tmp/sheaf/xif/paper/S1758SourceRetractionActual.lean\`, namespace
\`LeanFormal.IUT.XiFPaper.S1758SourceRetractionActual\`, 575 lines.

### Proved unconditionally (kernel closed)

1. \`S1758NatTrans_discrete_subsingleton\`, \`S1758Modification_subsingleton\`,
   \`S1758Modification_subsingleton_stack\`: modifications between strong
   transformations into a representable etale stack are subsingletons
   (components land in Mathlib's \`Discrete\` categories).
2. \`S1758ConeMorphism_compatibility_automatic\`: the compatibility equation of a
   cone morphism over the identity-point square is automatic, because the base
   corner of the square is the representable stack of \`Spec R'\`.
3. \`S1758TwoCell_ext_toSource\`: the recorded \`twoCell_ext\` of the
   identity-point witness collapses to "a 2-cell into the affine model is
   determined by its whiskering along \`toSource\`".
4. \`S1758Cone A f\` (tautological cone), \`S1758LiftCone A f\` (its lift),
   \`S1758WhiskerX\`, \`S1758WhiskerY\`: the explicit comparison isomorphisms of
   the two legs obtained from the recorded \`liftToX\`/\`liftToY\` of the identity
   cone, the base-change comparison \`commutes\`, and the unitors.
5. \`S1758ConeHom\`, \`S1758ConeHomInv\`, \`S1758LiftTwoCell\`,
   \`S1758LiftTwoCellInv\`, \`S1758LiftTwoCellIso\`: the two tautological cones of
   \`toSource ≫ S1758Lift A\` and of the identity are compared, and the
   \`liftTwoCell\` between their lifts is an isomorphism.  The cancellation is
   forced by discreteness of the representable model stack, not assumed.
6. \`S1758InverseTwoCell_unique\`, \`S1758RetractionIso_unique\`: any two
   candidate inverse 2-cells \`(vcomp toSource inv) ⟶ id\` are equal, and any two
   candidate retraction isomorphisms are equal.  The inverse 2-cell is therefore
   unique whenever it exists.

### The exact first missing statement

\`S1758LiftConeIso A\` (and \`S1758FirstMissing := ∀ A, S1758LiftConeIso A\`):

    ∀ (W) (f : W ⟶ Y (S1733Model A)),
      Nonempty (Iso (lift (tautological cone of f)) f)

i.e. **1-cell uniqueness / the counit of the two-pullback comparison**: the
lift of the cone induced by an actual 1-cell is 2-isomorphic to that 1-cell.
The data form is packaged as \`S1758LiftConeField\`; \`S1758LiftConeIso A\` is
equivalent to \`Nonempty (S1758LiftConeField A)\`
(\`S1758LiftConeIso_iff_nonempty_field\`).

Why this is exactly the missing piece, and why the recorded witness does not
give it: the identity-point \`TwoPullbackWitness\` supplies

* the lift of every cone and its two comparison 2-cells (object-level essential
  surjectivity);
* \`liftTwoCell\`, i.e. the induced 2-cell on cone morphisms (morphism-level
  essential surjectivity);
* \`twoCell_ext\` (faithfulness),

but it never produces a 2-cell whose source is a *1-cell* rather than a lift.
The required 2-cell \`vcomp toSource inv ⟶ id\` is exactly the counit of the
comparison \`Hom(W,P) ⟶ Cone(W)\`, and it is not among the fields.  The source
stack \`A.source\` is not representable, so the S1742 2-Yoneda comparison (which
would identify 2-isomorphism classes of endomorphisms of a representable stack
with scheme endomorphisms) cannot supply it either.

### Exactness of the missing statement (converse)

\`S1758LiftConeIso_of_retraction\`: from the *canonical* retraction
\`r ≫ s ≅ 1\` (with \`r = toSource\`, \`s = S1743Lift A\`) one reconstructs
1-cell uniqueness for every 1-cell \`f\`, by the explicit chain

    lift (cone f) ≅ lift (cone f) ≫ 1 ≅ lift (cone f) ≫ (r ≫ s)
      ≅ (lift (cone f) ≫ r) ≫ s ≅ (f ≫ r) ≫ s ≅ f ≫ (r ≫ s) ≅ f ≫ 1 ≅ f .

Consequently \`S1758FirstMissing_iff_retractionAtLift\`:
\`S1758FirstMissing ↔ S1758RetractionAtLift\`, where

    S1758RetractionAtLift :=
      ∀ A, Nonempty (Iso (vcomp (toSource) (S1743Lift A)) (id_{model}))

is precisely the S1743 target specialised to the canonical lift produced by the
two-pullback universal property.  So the missing statement is neither stronger
nor weaker than the missing half of stack representability at that lift.

### Reduction to the S1743 target

* \`S1758SourceRetractionAt_of_liftConeIso A : S1758LiftConeIso A → ∃ inv, ...\`
  (inverse 2-cell: the explicit composite
   \`(r ≫ s) ≅ lift (cone (r ≫ s)) ≅ lift (cone 1) ≅ 1\`);
* \`S1758SourceRetraction_of_firstMissing : S1758FirstMissing → S1743SourceRetraction\`;
* \`S1758SourceRetraction_of_retractionAtLift : S1758RetractionAtLift → S1743SourceRetraction\`;
* \`S1758SourceRepresentableAll_of_firstMissing :
   S1758FirstMissing → S1743SourceRepresentableAll\` (full item (a): both the
  section and the retraction half).

## Status

* statement_compiles = yes (target type \`S1743SourceRetraction\` and the missing
  statement written with the actual \`S1743Square\`, \`EtaleStackBaseChangePresentation\`,
  \`TwoPullbackWitness\`; no \`sorry\`, no axiom, no \`Shrink\`/\`ULift\`/\`PUnit\`).
* proof_body_checked = yes for all theorems listed above; no \`sorryAx\`.
* kernel_closed = yes for all theorems listed above: 17 \`#print axioms\` checks,
  every one depends only on \`[propext, Classical.choice, Quot.sound]\`.
* target_accepted = false: \`S1743SourceRetraction\` itself is **not** proved.
  The exact first missing statement is isolated and proved equivalent to the
  canonical retraction; no inhabitant of it is constructed and no 2-cell is faked.

## Evidence

* Lean: tmp/sheaf/xif/paper/S1758SourceRetractionActual.lean (575 lines),
  source SHA256 75EC6CA82118F5673D6BC411CF2649798A9600B91DEB4AB287C6D276D21DE0A6
* command:
  \`lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1758SourceRetractionActual.olean tmp/sheaf/xif/paper/S1758SourceRetractionActual.lean\`
* EXIT=0 (checker and olean build), no errors, no warnings
* olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1758SourceRetractionActual.olean
  (189384 bytes), SHA256
  805AAC5A3689B4E38539DB641C91E917F1F758068B2441804B76D90B257EC310
* logs: tmp/sheaf/xif/paper/logs/S1758_final.log (checks and axiom audit),
  tmp/sheaf/xif/paper/logs/S1758_olean_final.log

## Consumer

S1743 item (a) \`S1743SourceRetraction\` (and, through it, item (b)
\`S1743SliceFunctorMissing\`, S1733's \`S1733CoverSliceEquivalence\`,
\`EssentiallySmall.{0} S1728Cover\` and \`Category.{0,1} S1728Cover\`).
The package removes the ambiguity about what is missing: closing S1743 (a) is
exactly adding the 1-cell-uniqueness/counit field for the identity-point
two-pullback (or, equivalently, proving the canonical retraction).

## Next executable step

Add to the identity-point \`EtaleStackBaseChangePresentation\` a proof of
\`S1758LiftConeIso A\` for the cover at hand, or construct it for all covers by
extending \`TwoPullbackWitness\` with the counit of the comparison
\`Hom(W,P) ≃ Cone(W)\`.  Concretely: prove that the canonical lift \`s\` is a
retraction of \`toSource\`, i.e. \`Nonempty (Iso (vcomp toSource s) (id))\`
(\`S1758RetractionAtLift\`).  By \`S1758FirstMissing_iff_retractionAtLift\` this is
equivalent to the full missing statement, so no work is lost whichever form is
attacked.
