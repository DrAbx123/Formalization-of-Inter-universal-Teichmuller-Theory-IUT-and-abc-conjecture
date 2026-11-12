# S2058: D6(c) finite-etale API -- 2-isomorphism invariance proved, composition reduced to bicategorical pasting

Date: 2026-11-02 (Asia/Shanghai).  Layer: D6.  Consumer: S2043FirstMissingFiniteEtale
-> S1985ApexData.finiteEtale -> S1864/S1836 pseudopullback stack -> S1762 -> S1736.

## File

tmp/sheaf/xif/paper/S2058D6FiniteEtaleActual.lean  (513 lines)

Build: EXIT=0.  olean 774552 bytes at
.lake/build/lib/lean/tmp/sheaf/xif/paper/S2058D6FiniteEtaleActual.olean.
SHA256 of the source: 9A4288B46EE98C8FCB285AFE2F3121EFCC8F2744AC0C182E0B19D68DD28AB1B8.

Axiom audit (all printed in the file, no sorryAx anywhere):
- S2058IsoWitness, S2058IsoInvarianceProperty, S2058IsoInvarianceFiniteEtale,
  S2058SchemeRepresentableMapComp, S2058BaseChangeComp,
  S2058CompositionClosureOfPasting, S2058S2044CompositionClosure_of_pasting,
  S2058D6FiniteEtaleCertificate, S2058TransportHolds, S2058IsoInvarianceStatement:
  [propext, Classical.choice, Quot.sound].

## What is PROVED (new API, no fake witness)

1. 2-isomorphism invariance of EtaleStackRepresentableMorphismProperty in the
   stack morphism (S2058IsoInvarianceProperty, generic over the field), and its
   finite-etale specialization S2058IsoInvarianceFiniteEtale.  The base-change
   presentation (scheme, projection, projectionMap, toSource) is kept literally;
   only the horizontal leg of each square changes.  The transport of the
   TwoPullbackWitness (S2058IsoWitness with S2058OldCone/S2058OldHom) uses the
   exchange law Bicategory.whisker_exchange and nothing else.  twoCell_ext is
   invariant because it only mentions square.toX and square.toY.
   This closes S1892TransportHolds and S2046IsoInvarianceStatement
   (S2058TransportHolds, S2058IsoInvarianceStatement), which were unimplemented.

2. Composition of representable scheme maps (S2058SchemeRepresentableMapComp):
   the composite strong transformation represents the composite scheme
   morphism.  app_eq is proved by Cat.Hom.ext + Functor.ext + Discrete.ext (the
   object equality is definitional).

3. The composite base-change presentation (S2058BaseChangeComp): pullbackScheme
   = apex of the first presentation, projection = composite of the two scheme
   projections, projectionMap = composite representable map, toSource = first
   toSource, commutes = the associator/whiskering composite of the two recorded
   comparisons, isPullback = the pasted witness, hasProperty = closure of the
   scheme property under composition.

4. Composition closure of a representable morphism property modulo ONE named
   bicategorical input (S2058CompositionClosureOfPasting), and the paper-level
   S2044CompositionClosure from that input
   (S2058S2044CompositionClosure_of_pasting), and D6(c) from the two S2044
   fields (S2058D6FiniteEtaleCertificate): pasting + toA certificate give
   S2043FirstMissingFiniteEtale for every cospan.

## Exact first missing (not faked)

(A) S2058PastingStatement -- the pasting of two TwoPullbackWitnesses:
    for every pasting datum D (lower square P -> X over Ys, upper square
    Ys -> Zs over Y2) and witnesses of the two squares, a witness of the pasted
    square, given that 2-cells into the pasted apex D.P are subsingletons (this
    last hypothesis is automatic for representable apexes, which is the only
    case occurring in EtaleStackBaseChangePresentation).

    Status: UNPROVED.  Constructed so far (section 4 of the file,
    S2058Pasting): square1/square2/squareP, the cone conversions pastCone2 and
    pastCone1, the pasted lift pastLift, and the two projection comparisons
    pastLiftToX and pastLiftToY (with pastCone2_toX/_toY/_commutes).  Still to
    construct: pastCone2Hom (the action on cone morphisms of the upper square,
    whose compatibility is the associator_naturality_left computation), then
    pastCone1Hom (using w2.liftTwoCell_toX and the Iso inverse laws), then
    pastWitness, whose liftTwoCell_toY field is the distribution of
    (l1cell > (toY1 ; toY2)) across the two liftTwoCell_toY equations of the
    two given witnesses plus associator coherence.  All of this is pure
    bicategorical coherence, no geometry.

(B) S2058IsoCommaTwoPullback -- the general 2-universal property of the
    iso-comma square of two cover maps, for EVERY pseudo-cone over the cospan
    (not only the bicones handled by S1985 liftSite).  This is S1864 (d) in its
    general form; the tree has only the bicone case and the fibre-level
    property of S1893.  It is the genuinely geometric/2-categorical input needed
    to even state a base-change presentation of toA.

    Consequence: S2044ToAFiniteEtaleField is NOT proved.  The reason is
    precise: toA finite etaleness needs (B) plus the derived identification
    T x_A (A x_C B) = T x_C B as bicategorical pullbacks (a second pasting, of
    (B) with the g-map base change), which is not in the tree either.

## What is NOT claimed

- No TwoPullbackWitness is fabricated; S2058PastingStatement is a Type-valued
  obligation, uninhabited in the tree.
- No toA certificate is fabricated; S2044ToAFiniteEtaleField remains open.
- D6(c) is therefore reduced to (A) + (B); it is not closed.

## Attempt note (failed route, recorded for the next package)

A completion attempt for S2058Pasting.pastWitness (adding pastCone2Hom,
pastCone1Hom, and the liftTwoCell_toY distribution computation on top of
pastLiftToY) did not terminate: unfolding pastLiftToY (a composite Iso.trans of
an associator, a whiskering and two witness comparisons) with
simp only [pastLiftToY, ...] blows up, because the pastLift term it contains is
itself a w1.lift applied to a cone conversion and the unfolding is re-triggered
at every rewriting step.  The file was reverted to the verified version above.

Recommended next step: replace pastLiftToY by an explicit Iso structure whose
hom and inv are given componentwise (avoiding Iso.trans unfolding), or prove
pastLiftToY_hom / pastLiftToY_inv with rw-style rewriting (not simp) and then
close the liftTwoCell_toY goal with
rw [whiskerRight_comp, h1, comp_whiskerRight, h2]; simp only [Category.assoc].
The mathematical content is routine bicategorical coherence; only term-level
control at this definition-unfolding depth is the obstacle.
