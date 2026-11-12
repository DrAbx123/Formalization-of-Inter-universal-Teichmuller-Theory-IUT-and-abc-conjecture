# S1814: affine finite-etale covers of the S1726 orbicurve

Date: 2026-11-01

## Result

Target file: tmp/sheaf/xif/paper/S1814OrbicurveCoversAffineActual.lean

EXIT=0 (lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1814OrbicurveCoversAffineActual.olean)

Source SHA256:
  D8421C407C926ACB806B4B947C12ED2025811D518BD7554AD6059B0B1075BF54
Source bytes: 19294

Olean SHA256:
  04A1F1B70A02F8D8E5215BF53B428428A29410E46DD1A0C4AA40B47E0601DA9B
Olean bytes: 219984

Axioms: only propext, Classical.choice, Quot.sound (checked by #print axioms
for all key declarations). No sorry, no axiom, no admit, no Shrink/ULift/PUnit.

## Constructed unconditionally

* S1814SliceToCover : S1733Slice ⥤ FiniteEtaleCover (Spec R'), the forgetful
  functor from the affine finite-etale slice over Spec R' to finite etale
  covers of Spec R'. It is proved Faithful, Full, and EssSurj.

* S1814SliceEquiv : S1733Slice ≌ FiniteEtaleCover (Spec R'). This is a genuine
  equivalence: essential surjectivity uses S1799's theorem that every finite
  etale cover of the affine base Spec R' has affine carrier and is isomorphic
  to the cover Spec Γ(C, top). The inverse object map is explicit:
  S1814CoverToSlice C = Spec (coverSectionsFiniteEtale R' C), together with the
  finite-etale structure map of S1799. S1814SliceToCover_coverToSlice_iso
  proves the concrete isomorphism for every C.

* S1814AlgEquiv : (CommAlgCat.FiniteEtale R')^op ≌ FiniteEtaleCover (Spec R'),
  the S1799 affine finite-etale equivalence at the actual ring R'.

* S1814SliceAlgEquiv : S1733Slice ≌ (CommAlgCat.FiniteEtale R')^op, obtained by
  composing the two equivalences.

## Exact reduction of the requested orbicurve equivalence

Let S1728Cover = OrbicurveFiniteEtaleCover S1726Orbicurve with S1728's
2-isomorphism quotient category structure. The requested target is

  S1814OrbicurveAffineEquivalence : Prop
    = Nonempty (S1728Cover ≌ FiniteEtaleCover (Spec R')).

The file proves the following equivalences of propositions:

  S1814OrbicurveAffineEquivalence
    ↔ S1733CoverSliceEquivalence          (S1814_target_iff_slice)
    ↔ S1743SliceFunctorMissing            (S1814_target_iff_sliceFunctorMissing)
    ↔ S1814FirstMissing
        = ∃ F : S1728Cover ⥤ S1733Slice,
            Nonempty F.FullyFaithful ∧ F.EssSurj
                                          (S1814_target_iff_firstMissing).

In words: the target is exactly the existing S1733/S1743 affine-slice
comparison, composed with the genuinely constructed equivalence
S1814SliceEquiv. No new gap is introduced, and the target is not weakened.

## Precise missing data on the canonical route

The canonical comparison functor is S1757Functor h, with object map S1743Object
(the identity-point base-change model). The file names and relates the three
missing statements:

* stack representation:
  S1814StackRepresentation = S1756FirstMissing, proved equivalent to
  S1743SourceRetraction (S1814_stackRepresentation_iff_sourceRetraction). It
  supplies the lift section h : S1757LiftSection.

* cover-map comparison:
  S1814CoverMapComparison = S1755ModelHomEquivMissing. It gives bijectivity of
  S1755's model-hom extraction (S1814_coverMapComparison_bijective) and
  S1733AffineCoverModelMissing (S1814_affineCoverModel_of_comparison).
  Full faithfulness of S1757Functor on 2-isomorphism classes is a further
  compatibility statement, not a consequence of the raw bijection alone
  (S1787 is the detailed analysis; S1801 refutes the generic two-pullback
  schema).

* essential surjectivity:
  S1814EssSurjMissing = S1757EssSurjMissing: every affine finite etale scheme
  over Spec R' is the model of an actual cover.

The conditional construction:

  S1814_target_of_canonicalData
    (hrep : S1756FirstMissing)
    (hff : (S1757Functor (S1814_liftSection_of_firstMissing hrep)).FullyFaithful)
    (hess : S1757EssSurjMissing)
    : S1814OrbicurveAffineEquivalence.

Also recorded:

  S1814_target_of_liftSection
  S1814_target_of_sliceComparison : S1743CoverSliceComparison →
    S1814OrbicurveAffineEquivalence.

## Honest boundary

The equivalence OrbicurveFiniteEtaleCover S1726Orbicurve ≌
FiniteEtaleCover (Spec R') is NOT constructed. It is proved equivalent to the
existing missing affine-slice equivalence. The stack representation, the
cover-map comparison on 2-iso classes, and the essential-surjectivity
statement are not inhabited here. No fake equivalence, no arbitrary data, no
new axiom was used.

## Recommended next step

Attack S1743CoverSliceComparison (or equivalently S1814FirstMissing), with the
object map fixed to S1743Object. The shortest known decomposition is:

1. S1756FirstMissing (equivalently S1743SourceRetraction) for the lift section;
2. full faithfulness of S1757Functor h, i.e. the 2-iso-class comparison of
   cover maps with maps of affine models;
3. S1757EssSurjMissing (extension from affine finite-etale schemes to covers).

S1814SliceEquiv then transports any such equivalence directly to the requested
FiniteEtaleCover (Spec R') target.
