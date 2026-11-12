# S1831: the strong 2-universal property of the actual finite etale base-change square (geometric / affine route)

Status: proof file compiled (EXIT=0, no warnings, no sorryAx, axioms trio only).
The strong 2-universal property is **not** proved; the exact first missing statement
is named and proved equivalent to the target, and is reduced to the apex of the square
and to an equation of finite etale `R'`-algebras.

Consumer: S1827/S1804/S1784/S1756/S1758/S1743 closure route (S1827FirstMissing,
S1804FirstMissing, S1784LiftEssSurj, S1756Unit/S1756End, S1758FirstMissing,
S1743SourceRetraction, S1756SourceRepresentableAll) and S1816/S1781/S1799
(affine model / finite etale cover of `Spec R'` / algebra side).

## 1. The target, locked

    S1831StrongSquare A := S1827ConeEssSurj A
                        = S1784LiftEssSurj A   (the missing half of the
                          2-dimensional universal property of the identity-point
                          square  P = Y(S_A) -> A.source,  P -> Y(Spec R'),  A.map, id)

Proved equivalent to, for every cover `A`:

* `S1756Unit A` (the unit 2-cell `toSource ; lift ≅ 1`),
* `S1756End A = 1` (the identity-point self-endomorphism of `S_A`),
* `S1827ComparisonQuasiEquiv A` (the comparison with the actual 2-pullback, apex
  `A.source`, is a quasi-equivalence),
* `S1804RecordedActual A`, and S1784's counit data `S1784CounitData A`
  (the two 2-cells at the square's own cone).

`S1831FirstMissing := ∀ A, S1831StrongSquare A` is proved equivalent to
S1827FirstMissing, S1804FirstMissing, S1756FirstMissing, S1743SourceRetraction,
S1758FirstMissing and `∀ A, S1827ComparisonQuasiEquiv A`, and implies
S1756SourceRepresentableAll.  Axioms: trio only.

## 2. What is new and unconditional

1. **Apex reduction.** `S1831ApexRigid A`: every endomorphism `f` of the
   representable stack `P = Y(S_A)` whose two projections agree with the square's own
   projections is 2-isomorphic to the identity.  Proved

       S1831StrongSquare A  ↔  S1831ApexRigid A.

   So the missing input can be tested at the apex alone; no quantification over
   arbitrary test stacks remains.

2. **The missing 2-cells in scheme form.**  The own-cone lift `S1784Counit A : P -> P`
   has 2-Yoneda evaluation

       S1831OwnConeEval A : S_A ⟶ S_A

   and `S1831OwnConeEval_projection` proves unconditionally that it is a morphism over
   `Spec R'` (the own-cone analogue of `S1756End_projection`).  With
   `S1831OwnConeLift_iff_eval`, `S1831OwnConeLift_iff_end`:

       S1831StrongSquare A  ↔  S1831OwnConeEval A = 1 ∧ S1756End A = 1
                            ↔  S1831OwnConeEval A = 1 ∧ S1831OwnConeEval A = S1756End A.

   So the whole missing 2-universal property is two equations between endomorphisms of
   the affine model.

3. **Affine / finite-etale-algebra form (S1781 + S1799 + S1816).**
   `S1831AlgEnd A : S1781Obj A ⟶ S1781Obj A` is the endomorphism of the finite etale
   `R'`-algebra `Gamma(S_A)` induced by `S1756End A`, and

       S1831StrongSquare A  ↔  S1831AlgEnd A = 1

   (`S1831AlgEnd_eq_one_iff` uses S1781's `S1781_modelMap_ext`: `Spec`/`Gamma` are
   mutually inverse on affine schemes).  Through S1799's actual equivalence
   `(FiniteEtale R')^op ≌ FiniteEtaleCover (Spec R')` this transports to
   `S1831CoverEnd A` on the actual finite etale cover of `Spec R'`:

       S1831StrongSquare A  ↔  S1831CoverEnd A = 1.

   `S1831CoverCarrier_iso` records the affine carrier bridge between the actual cover
   `S1816Obj A` and `Spec Gamma(S_A)`.

4. **Retraction picture.**  `S1831Comparison_section`: `lift ; toSource ≅ 1`
   (S1784).  `S1831Comparison_essSurj_objects`: every 1-cell `W -> A.source` is the
   composite of a 1-cell `W -> Y(S_A)` with `toSource`.  So the model *covers* the
   source; the target is exactly the question whether that cover is also injective
   (1-cell uniqueness), not surjectivity.

5. **Positive instance.**  `S1831StrongSquare_of_mono`: if `S_A -> Spec R'` is a
   monomorphism the target holds (S1827's criterion, re-exported), and
   `S1831OwnConeEval_eq_one_of_mono` discharges the first missing 2-cell directly.

## 3. The exact first missing statement

    S1831FirstMissing  :  ∀ A, S1831ApexRigid A
    ≍  ∀ A, S1827ConeEssSurj A
    ≍  ∀ A, (S1831OwnConeEval A = 1 ∧ S1756End A = 1)          (scheme equations)
    ≍  ∀ A, S1831AlgEnd A = 1                                  (finite etale R'-algebra)
    ≍  ∀ A, S1831CoverEnd A = 1                                (finite etale cover of Spec R')

In words: **1-cell uniqueness of the recorded identity-point square at its own apex** -
the lift of the square's own cone must be the identity (and so must `toSource ; lift`).

Why it is not obtained here:

* the seven recorded `TwoPullbackWitness` fields produce the lift and 2-cell
  extensionality, but no comparison of two *1-cells*; S1801's degenerate square
  satisfies all seven fields and its cone comparison is not essentially surjective
  (`S1831RecordedWitnessInsufficient`, `S1831WitnessNotIso` re-exported from S1827).
  Exactly as S1827 notes, S1801's model has a constant apex whereas here the apex is the
  representable `Y(S_A)`, so that refutation settles the 2-categorical-algebra question
  only; it is not a counterexample inside the cover situation.
* closing the target therefore needs either the definition change of
  `TwoPullbackWitness` to the full 2-universal property (excluded by the user: the
  object must stay unchanged) or an independent geometric theorem saying that the
  identity-point presentation square is a genuine 2-pullback, i.e. that the
  representably finite etale stack `A.source` is represented by its identity-point model
  `S_A` and not merely a retract of it.  No such theorem is in the tree; S1816's
  essential surjectivity and fullness are likewise absent.

No fake 2-cell, no fake equivalence, no new axiom, no `sorry`, no `Shrink`/`ULift`/`PUnit`;
`TwoPullbackWitness` is unchanged.

## 4. Next step

Prove one of the two apex equations of §3.  Candidate routes, in the order the tree
supports them: (i) use the base-change presentations at the *other* scheme points
`T -> Spec R'` together with the stack condition `A.source.isStack` to upgrade the
identity-point weak square to 1-cell uniqueness; (ii) construct a cover `A` with
`S1831OwnConeEval A ≠ 1` (a proper component projection of `S_A`), which would refute
the target for the unchanged definition and settle the question in the negative;
(iii) prove `S1831AlgEnd A = 1` on the algebra side, i.e. that the idempotent
`R'`-algebra endomorphism of `Gamma(S_A)` selected by the identity-point presentation
is not a proper projection.

## 5. Evidence

* File: `tmp/sheaf/xif/paper/S1831StrongSquareGeometricActual.lean`,
  31313 bytes, 649 lines, 48 named `S1831*` declarations.
* EXIT=0, zero errors, zero warnings, no `sorryAx`.
* `#print axioms` on all 31 checked declarations: `propext`, `Classical.choice`,
  `Quot.sound` only.
* Source SHA256: `E748FD19AA0664C8E0FDB2206A8EB62337FE3AA682761C1DE43DD19B56345A3B`.
* Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1831StrongSquareGeometricActual.olean`,
  153048 bytes, SHA256 `12E6BD8E6DE5E93890F4CC8F0A27CC6BE9DBCEB380C5DF6ACF95BC87B7C7D270`.
* Compile command: `lake env lean -j1 -R D:\lean -o <olean> tmp/sheaf/xif/paper/S1831StrongSquareGeometricActual.lean`.

Honest labels: `statement_compiles`=yes, `proof_body_checked`=yes (for the proved
statements), `kernel_closed`=yes (trio axioms), `target_accepted`=false (the strong
2-universal property is named, not proved).
