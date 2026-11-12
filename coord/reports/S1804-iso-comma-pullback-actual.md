# S1804 - the actual iso-comma pullback of (A.map, id) and the exact first missing

Date: 2026-11-01.  Status: **missing** for the unconditional target (S1756FirstMissing
is not proved), but the iso-comma construction, the actual pullback universal
property, and the exact equivalence with the already-recorded missing statements
are proved.  No fake 2-cell, no fake equivalence, no sorry/axiom.

## Deliverable

| item | value |
|---|---|
| file | tmp/sheaf/xif/paper/S1804IsoCommaPullbackActual.lean |
| lines | 381 |
| source SHA256 | 39B14ECF759F09D8281E26A36FC3FB06700A2084FC7F7921C513AF5A6B5DCE54 |
| compile | lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1804IsoCommaPullbackActual.olean tmp/sheaf/xif/paper/S1804IsoCommaPullbackActual.lean |
| EXIT | 0 (no error, no warning, no sorry/sorryAx) |
| olean | .lake/build/lib/lean/tmp/sheaf/xif/paper/S1804IsoCommaPullbackActual.olean (245576 bytes) |
| olean SHA256 | E8E79847875F449C0AD78AC3DF64F247285DB4C983C75E7EA90C6140B1636521 |
| import probe | tmp/sheaf/xif/paper/_S1804ImportProbe.lean, EXIT=0 |
| axioms | propext, Classical.choice, Quot.sound only (27 #print axioms checks) |

## What is constructed / proved

1. **Iso-comma fiber.**  For a test object U,

     S1804IsoCommaFiber A U = Comma (A.map.app U) (baseId U)

   has objects (x, y, h) with x : source(U), y : U -> Spec R' and
   h : A.map(x) -> y.  Because the base fiber is the discrete category
   Discrete(U -> Spec R'), every h is an isomorphism; this is the requested
   iso-comma model.  The projection to the source is proved Full, Faithful and
   EssSurj, hence

     S1804IsoCommaFiberEquiv A U : S1804IsoCommaFiber A U = S1804SourceFiber A U

   (an actual equivalence of categories).  The named pullback object
   S1804IsoCommaPullback A is the source, and S1804IsoCommaPullback_fiber
   records the fiber equivalence.

2. **Actual 2-pullback.**  The actual pullback square
   S1804SourceSquare A has apex the source, legs id_X and A.map.  Its lift of a
   cone c is c.toX, with both projection 2-isomorphisms
   S1804SourceLiftToX / S1804SourceLiftToY.  S1804Source_isPullback proves the
   1-cell universal property (the same property S1784LiftEssSurj asks of the
   recorded square): any f whose two projections agree with c is 2-isomorphic
   to c.toX.  S1804SourceCone_proj records the object-level essential
   surjectivity (every cone is the canonical cone of its source leg on the first
   projection, and the second projection is recovered from c.commutes).

3. **The recorded square is actual iff the unit exists.**  New theorem
   S1804LiftEssSurj_iff_unit:

     S1784LiftEssSurj A  <->  S1756Unit A.

   The missing direction (unit -> LiftEssSurj) lifts any 2-isomorphism of
   toSource-whiskerings through the unit and the two triangle isomorphisms; no
   bicategorical cancellation is assumed.  Consequences:

     S1784LiftEssSurj A <-> S1756Unit A
                        <-> S1756End A = id
                        <-> S1758LiftConeIso A
                        <-> S1784CounitData A.

   S1804CounitData_of_recordedActual / S1804RecordedActual_of_counitData /
   S1804RecordedActual_iff_counitData prove the CounitData equivalence.

4. **Exactness of the first missing statement.**

     S1804FirstMissing <-> S1756FirstMissing
                       <-> S1743SourceRetraction
                       <-> S1758FirstMissing
                       <-> forall A, S1784LiftPointSurj A.

   Conditional closures: S1804FirstMissing_to_S1756FirstMissing,
   S1804FirstMissing_to_sourceRetraction,
   S1804FirstMissing_to_sourceRepresentableAll, and
   S1804StackEquivOfRecordedActual (the quasi-equivalence P = source).

## The exact first missing statement

The recorded identity-point presentation has a canonical comparison
toSource : P -> source.  The actual pullback is the source (Section 2), so the
recorded presentation is the actual pullback iff this comparison is an
equivalence, i.e. iff the missing unit 2-cell

    toSource ; lift = id_P

exists.  By Section 3 this is exactly S1784LiftEssSurj, exactly S1758LiftConeIso,
and exactly S1784CounitData.  This is the first missing statement; no inhabitant
is constructed.

## Honest boundary

* The pseudofunctor-level packaging of the iso-comma as a separate pseudofunctor
  is not built: by Section 2 the actual pullback pseudofunctor is the source
  itself, and the iso-comma appears as its fiber model (Section 1).  No claim of
  a separate P' with its own transition data is made.
* The seven recorded fields still do not imply the missing statement; the Cat
  countermodel in the S1784 header remains the reason.  The new content is that
  the missing statement is equivalent to actuality of the recorded pullback, and
  that the actual pullback and its iso-comma fibers are constructed.
* No AUDIT_LEDGER / STATE / queue edit was made (to avoid concurrent coordinator
  conflicts); please have the coordinator record this report.

## Shared-tree note

During the run, LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31RootLemmas.lean
was temporarily uncompilable against the working-tree SourceDefinition31Boundary.lean
(removed sectionMap/section_right_inverse fields) and its olean was missing; imports
of S1784/S1758 failed.  The InitialTheta owners rebuilt Boundary, Quantifiers and
RootLemmas during the run; after that the S1804 compile above succeeded (EXIT=0).
This is not an S1804 assumption.

## Next executable step

Prove the missing unit (equivalently S1804FirstMissing / S1784LiftEssSurj) for one
cover, e.g. via the affine finite-etale algebra comparison (S1799/S1781) or the
finite-etale descent route, and feed it to S1804FirstMissing_to_S1756FirstMissing.
