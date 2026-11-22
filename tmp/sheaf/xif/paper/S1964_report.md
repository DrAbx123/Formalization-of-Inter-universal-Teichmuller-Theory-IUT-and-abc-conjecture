# S1964: the quotient C_F = X_F/{+-1} — honest status, uniqueness, and the fixed locus

File: `tmp/sheaf/xif/paper/S1964QuotientCFActual.lean` (470 lines, 24498 bytes)

- EXIT = 0 (`lake env lean -j1 -R D:/lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1964QuotientCFActual.olean tmp/sheaf/xif/paper/S1964QuotientCFActual.lean`)
- no errors, no warnings, no `sorryAx`
- olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1964QuotientCFActual.olean` (570216 bytes),
  SHA256 `7385C165C46102994BF3944A6456DFDFF1B3AAB65D4221E504BB3D7FE46DC854`
- SHA256(source) = `4E7FB249DB4184B9E30E08C441E20295E262729D7CA2DE86EF42BD39AB32752F`
- axioms: all 28 audited declarations report only `propext`, `Classical.choice`,
  `Quot.sound` (one reports `propext` alone).  No `sorry`, no `admit`, no new axiom,
  no postulated quotient.  Log: `tmp/sheaf/xif/paper/logs/S1964_compile.log`.

## What is constructed / proved (genuine, no postulate)

### 1. The fixed locus of the actual elliptic involution

The affine Weierstrass model of E' is `y^2 = x^3 + (61/64) x^2 - (125/64) x`.  The
cubic factors as `x (x-1) (x + 125/64)` (`S1964Cubic_factors`), so:

* the *third* two-torsion point `(-125/64, 0)` is an actual F'-point
  (`S1964Equation_neg125`; the two others were already in S1726);
* **any** affine point over F' with `y = 0` has abscissa `0`, `1` or `-125/64`
  (`S1964TwoTorsion_abscissa`): the model has exactly three affine two-torsion points,
  all F'-rational;
* the three points are pairwise distinct (`S1964TwoTorsion_pairwise_distinct`);
* the elliptic negation `p |-> -p` is defined on actual affine points and is an
  involution (`S1964Neg`, `S1964Neg_involutive`); its fixed points are exactly the
  points with `y = 0` (`S1964Neg_eq_self_iff`), and **the fixed points of the actual
  involution on the affine model are exactly the three two-torsion points**
  (`S1964FixedPoint_cases`);
* at the level of the actual scheme endomorphism `S1898AffineEndo`, a section is fixed
  iff its y-coordinate vanishes (`S1964Section_fixed_iff`,
  `S1964FixedAffinePoints_classified`), and the three two-torsion sections are fixed
  (`S1964TwoTorsionSections_fixed`).

This is the actual geometric input for the quotient: the honest quotient
`X_F/{+-1}` has one order-two stacky point over each of these three points, and one
cusp (the image of the origin in the projective closure; the origin is removed from
`X_F`).  Caveat, stated explicitly: the *order-two ramification* assertion is the
standard local computation `y |-> -y` (`S1898CoordEndo_y` is in the tree); the file
does **not** formalize a stacky-point/inertia theory (none exists in the tree), so the
"stacky point" conclusion is documented, not formalized.

### 2. The honest signature type

`S1964HonestQuotientSignature = (0; [2,2,2]; 1)` (genus 0, three order-two stacky
points, one puncture), with orbifold Euler characteristic `-1/2`
(`S1964HonestQuotientSignature_euler`), hence hyperbolic
(`S1964HonestQuotientSignature_hyperbolic`).  It is *not* the paper label
`(1,1)^pm = (1; [2]; 0)` (`S1964HonestSignature_ne_paper`).

The coarse quotient `(0; []; 1)` has Euler characteristic `1`, so **a coarse
(non-stacky) quotient could not be a hyperbolic orbicurve at all**
(`S1964CoarseQuotientSignature_not_hyperbolic`): the honest `C_F` must be a genuine
stacky quotient, not a quotient sheaf / quotient scheme.

## 3. Signature labels are not determined by the fiber

`S1964SignatureLabelsNotDeterminedByFiber`: two hyperbolic orbicurves over F' with the
**same** etale stack fiber and different signatures exist (the paper label on one, the
honest label on the other).  Hence `HyperbolicOrbicurve.signature` is metadata attached
to a fiber: the paper target's `cF_signature` field cannot be a *consequence* of any
construction of the quotient fiber, and it cannot be used to test paper-faithfulness.
This refines the S1886 `S1886CFMetadataRelabel` observation to the quotient setting.

## 4. The quotient structure and its uniqueness

* `S1964QuotientStructure l A` = (quotient orbicurve `cF`, sign-invariant morphism
  `X_F -> cF`, `OrbicurveSignQuotientWitness`) — the paper target *without* the
  signature label.
* `S1964QuotientStructure.ofPaper : S1932CFQuotient l A -> S1964QuotientStructure l A`:
  the paper target's substantive content is the quotient structure.
* **`S1964QuotientUnique`**: two quotient structures for the same action factor through
  each other, with 2-isomorphisms `(q_T ; f) ~ q_S` and `(q_S ; g) ~ q_T` compatible
  with the two quotient morphisms.  So the missing object is unique up to 2-isomorphism
  if it exists.
* `S1964CFQuotientAt l A s hs`: the signature-parameterized target;
  `S1964CFQuotientAt_iff_paper` shows the paper target is the instance at the paper
  label, and `S1964FirstMissing_ofAt` / `S1964FirstMissing_ofHonest` show every label
  reduces to the same quotient structure.
* `S1964FirstMissing l A := Nonempty (S1964QuotientStructure l A)` is *the* exact first
  missing datum; `S1964FirstMissing_ofPaper` proves the paper target implies it.

**Caveat, one direction only.**  The reduction proved here is
paper target ⇒ quotient structure (and, for every label `s`, labelled target ⇒ quotient
structure).  The *reverse* direction — rebuilding a quotient structure with a different
signature label on the same fiber — is **not** formalized in this file: the obstruction
is dependent-type transport (the fields of `OrbicurveSignInvariantMorphism` /
`OrbicurveSignQuotientWitness` live over `cF.stack.fiber`, so changing
`cfg.signature` requires either definitional equality of the two orbicurve structures or
an explicit transport of all fields; `realizedHyperbolicOrbicurve_stack_fiber` gives
the fiber equality only with `rfl`, and the `cocycle` field type did not transport
definitionally in this session).  S1886's `S1886CFMetadataRelabel` proves the analogous
relabeling for the S1726 fiber, so the label is certainly expected to be free; but this
file does not claim it.  Consequence: the *necessary* reduction (paper ⇒ structure) and
the label-independence of the *fiber* (section 3) are proved; the *sufficiency* of the
quotient structure for the paper target is not.

## Exact first missing (the answer to the task)

The quotient stack is **not constructed**, and it is **not postulated**.  The first
missing object is a `S1964QuotientStructure l A`, i.e. the category-valued etale stack

    [X_F / {+-1}]  =  colim over B(Z/2) of X_F

together with the quotient morphism and its bicategorical universal property.  What is
absent from the tree and Mathlib is the construction, in four concrete steps:

1. the pointwise lax colimit (Grothendieck construction) of the sign action
   `A.diagram` on the `Cat`-valued pseudofunctor `X_F.fiber` — no such construction
   for a group acting on a category-valued etale stack exists;
2. the functoriality/coherence of that construction in the test scheme;
3. **descent**: `Pseudofunctor.IsStack` for the resulting pseudofunctor, i.e.
   stackification of the pointwise colimit.  Mathlib has the bare class
   (`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean:49`) with no instance for a
   quotient; the tree has `IsStack` only for representable (discrete) fibers
   (S1419/S1726) and sheaf-valued fibers, never for a colimit of an action;
4. the bicategorical universal property itself (`descend` / `factor` /
   `descendTwoCell` / `twoCellExt`), which becomes available only after 1-3.

Steps 1-3 are exactly the "quotient-stack route" already recorded as unavailable in
S1761 and S1792.  Attempting to shortcut any of them (e.g. using the pointwise
"trivial-torsor" presheaf, or the coarse quotient sheaf) would produce an object that
is *not* the quotient: the pointwise presheaf fails etale descent, and the coarse
quotient is not even hyperbolic (section 2).

## Findings for the lead

1. **The paper target's signature field is metadata, not an obstruction.**  By
   `S1964SignatureLabelsNotDeterminedByFiber` the field cannot be forced by geometry in
   the present design, and the substantive missing content of the paper target is exactly
   `S1964QuotientStructure` (`S1964FirstMissing_ofPaper`, `S1964FirstMissing_ofAt`).
   A "construct the quotient" task should therefore be stated as constructing
   `S1964QuotientStructure`, with the signature question treated separately.  Note the
   one-directional caveat in section 4: paper ⇒ structure is proved, structure ⇒
   paper-labelled object (relabeling) is not formalized here.
2. **The honest signature of the actual S1726 model is `(0; [2,2,2]; 1)`, not
   `(1; [2]; 0)`.**  The three two-torsion points are F'-rational and fixed by `[-1]`
   (section 1), and the origin (the puncture) is the fourth fixed point of the
   projective involution.  The label `(1,1)^pm` recorded as
   `sourceTypeOneOnePlusMinus` (genus 1, one order-2 stacky point, no punctures) is
   therefore **not** the geometric signature of the quotient of the constructed model.
   This does not contradict anything in the tree (the signature is not tied to the
   stack by any theorem), but it means that closing `S1886PaperCF` by any route cannot
   also be evidence for paper-faithfulness of that label.  If the paper's `(1,1)^{+-}`
   notation means something other than `sourceTypeOneOnePlusMinus`, the transcription
   should be re-checked (S1360/S1374 history, `SourceDefinition31Quantifiers.lean:295`).
3. **The reduction is stable**: any future construction of `[X_F/{+-1}]` closes the
   S1932 target *up to the label*, and the quotient is then unique
   (`S1964QuotientUnique`), so a single construction is enough and no choice is
   involved.

## Compile status

- `statement_compiles`: yes (EXIT 0)
- `proof_body_checked`: yes (no `sorryAx` anywhere in the log)
- `kernel_closed`: yes for every declaration in the file (axioms = the three allowed)
- `target_accepted`: no.  The quotient stack is not constructed; the exact missing
  datum is `S1964FirstMissing` (steps 1-4 above).  Nothing is faked: no quotient, no
  signature assertion, no axiom.
