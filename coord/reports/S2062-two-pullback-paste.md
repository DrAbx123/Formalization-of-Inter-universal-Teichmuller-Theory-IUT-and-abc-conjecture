# S2062: TwoPullbackWitness.paste and base-change presentation composition

Date: 2026-11-02 (Asia/Shanghai).  Scope: the two missing API items of the
S2046/S2050 D6(c) list, implemented in Lean.

## Layer / domain / direction / consumer

- Layer: D6 (finite-etale cover stack geometry), API layer.
- Consumer: S2046CompositionStatement (representable finite etaleness is closed
  under composition of stack morphisms), i.e. S2044CompositionClosure and hence
  S2043/S2042/S1864(c).  Item 1 of the S2046 lemma list (presentation
  composition) and item 2 (witness pasting).
- Direction: actual construction.  No Prop/Nonempty gate, no fake witness, no
  new axiom, no sorry.

## File and build evidence

tmp/sheaf/xif/paper/S2062TwoPullbackPasteActual.lean (530 lines, 25009 bytes)

- import: Iut.Foundations.Orbicurve (no dependency on the LeanFormal paper chain)
- compile: lake env lean -j1 -R D:\lean -o <olean> <file>  =>  EXIT=0
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S2062TwoPullbackPasteActual.olean
  (353336 bytes)
- SHA256 of the Lean source:
  0D3F1547F65B4A0A9EC67677652E51E74D1A5FB6BA2D51C0235D84149763A02C
- log: tmp/sheaf/xif/paper/logs/S2062_final3.log
- axiom audit (printed in the file): every declaration depends only on
  [propext, Classical.choice, Quot.sound]; no sorryAx.  The three coherence
  lemmas use [propext, Quot.sound] or [propext] only.

## What is proved

1. Iut.EtalePseudofunctorSquare.pasteCommutes / pasteSquare: the 2-commutativity
   and the square of the vertical pasting.  Apex/top legs as in the S1892/S2050
   shape; the shared leg is literally bottom.toX (this is the form the consumer
   uses and avoids a transport).
2. Cone-level pasting: pasteConeBottom (a cone over the pasted square gives a
   cone over the lower square), pasteConeTop (its wbottom-lift then gives a cone
   over the upper square), pasteConeMorphismBottom / pasteConeMorphismTop on cone
   morphisms.  The lift is the two-step lift.
3. Iut.EtalePseudofunctorSquare.TwoPullbackWitness.paste: all seven fields of
   the witness for the pasted square (lift, liftToX, liftToY, liftTwoCell,
   liftTwoCell_toX, liftTwoCell_toY, twoCell_ext).  liftToY is the
   associator/whisker composite of the two witnesses; liftTwoCell_toX is
   wtop.liftTwoCell_toX; liftTwoCell_toY is the composite
   (whiskerRight_comp + comp_whiskerRight + both liftTwoCell_toY).
4. The three coherence inputs are proved as statements about an arbitrary
   bicategory in namespace Iut.PasteCoherence (pasteCompatBottom,
   pasteCompatTop, pasteCompatToY).  Doing them at the level of a generic
   Bicategory was necessary: in the pseudofunctor bicategory the tree carries
   two Category structures on strong transformations
   (EtaleStackPseudofunctor.homCategory and the scoped
   Pseudofunctor.StrongTrans.homCategory), and the concrete goals are not
   type-correct at the instances transparency level inside tactics, so tactic
   proofs on them silently produce enormous, non-printing terms.  The generic
   lemmas elaborate in milliseconds and are applied by a single exact.
5. Iut.EtalePseudofunctorSquare.subsingleton_catHom₂ and
   subsingleton_strongTrans_schemeRepresentable: every 2-cell into a
   representable etale pseudofunctor is trivial (its values are discrete
   categories).
6. Iut.SchemeRepresentableMap.comp: the composite projection map (vcomp of the
   two strong transformations plus the app equation).
7. Iut.EtaleStackBaseChangePresentation.comp: the presentation of
   vcomp f g at q from a presentation of g at q and of f at the induced point.
   apex = pullbackScheme of the f-presentation, projection = the composite of
   the two projections, toSource = the toSource of the f-presentation, commutes
   = pasteCommutes, isPullback = TwoPullbackWitness.paste applied to the two
   witnesses.  No extra hypotheses.

## Honest boundary: the unconditional paste is not derivable

The composite square's twoCell_ext requires joint faithfulness of
(top.toX, toY ; bottom.toY).  From the two witnesses one gets
(a |> bottom.toY) = (b |> bottom.toY); cancelling the right whiskering by
bottom.toY is not available and is false in general (in the bicategory of
categories take bottom.toY the constant functor to the terminal category and
bottom.toX faithful).  So the general paste cannot be proved from the recorded
fields, and a weakening of the witness is not allowed.  paste therefore takes
the faithful-apex input

  hsub : forall {W f g}, Subsingleton (f -> g)

which is exactly the missing half of twoCell_ext.  For the D6(c) consumer the
apex is a representable pseudofunctor, where hsub is proved outright
(item 5), so EtaleStackBaseChangePresentation.comp is unconditional.

Exact remaining API for the unconditional paste (single item):

  forall {a b c} (g : b -> c) {f f' : a -> b} (eta th : f -> f'),
    eta |> g = th |> g -> eta = th

(right-whiskering cancellation, equivalently the full 2-dimensional universal
property of the recorded square).  This is recorded in the file docstring; it is
not needed by the D6(c) chain.

## What is NOT claimed

- S2050's S2050PasteStatement (for an arbitrary candidate composite square) is
  not asserted: it is unprovable as stated, because the composite square enters
  as unrelated data.  The file constructs the composite square and its
  commutes instead.
- S2046CompositionStatement is not yet written in this file (it is now a
  mechanical assembly: EtaleStackBaseChangePresentation.comp + Over.comp_left +
  S2048_isFinite_and_etale_comp).  No claim is made that it compiles.
- Nothing was added to Iut/Foundations/Orbicurve.lean.  The declarations live in
  the Iut namespace from the tmp file and only depend on Orbicurve, so they can
  be moved into that file without change.

## Next step

Add S2062CompositionStatement : S2046CompositionStatement by assembling
EtaleStackBaseChangePresentation.comp with S2048_isFinite_and_etale_comp (the
projection property needs only Over.comp_left), then promote
pasteCommutes/pasteSquare/pasteCone*/TwoPullbackWitness.paste,
subsingleton_*, SchemeRepresentableMap.comp and
EtaleStackBaseChangePresentation.comp into Iut/Foundations/Orbicurve.lean.
