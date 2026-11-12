# S1744: actual Category.{0,1} assembly from the S1733 missing statements

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1744Category01AssemblyActual.lean

EXIT=0 (lake env lean, no error, no warning, no sorryAx)

SHA256: 0EC7647D9E64DF3852D6FE7207D92A2047AF385D56AE86338ABED42EF263224E

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1744Category01AssemblyActual.olean (235640 bytes)

Lines: 537.

## Verdict

Neither S1733AffineCoverModel nor S1733CoverSliceEquivalence is inhabited in this
package.  No fake: no sorry, no axiom, no Shrink/ULift/PUnit, no fake category.
The two S1733 missing statements are replaced by an exact, smaller residual list,
and one of the two directions of the affine-cover comparison is now actually
constructed.

## What is constructed unconditionally

1. Affineness of the canonical base-change model (new; S1733 only had
   IsFinite and Etale of the model projection):

   * S1744Base_isAffine : IsAffine (Over.left S1726AffineOver)
   * S1744Model_isAffine : forall A, IsAffine (Over.left (S1733Model A))
     (from IsFinite => IsAffineHom and isAffine_of_isAffineHom).

2. S1744ModelData: all six geometric fields of S1733AffineCoverModel except
   homEquiv, with unconditional inhabitant S1744CanonicalModelData and
   S1744ModelData_nonempty : Nonempty S1744ModelData.

3. The object-level slice comparison: for every actual cover,
   S1744SliceObject A : S1733Slice (the affine model Spec Gamma(model A) over
   the base, built with Scheme.isoSpec), S1744SliceObject_prop (finite etale
   structure morphism), S1744SliceIdentityObject : S1733Slice and
   S1744Slice_nonempty : Nonempty S1733Slice.

4. The action of cover maps on the canonical models (the "functoriality"
   direction of the missing hom comparison), built from the two parallel
   packages S1742 and S1743:

   * S1744BaseChange A : the identity-point base-change presentation of A;
   * S1744ModelMapOfCoverMap A B f : S1733Model A --> S1733Model B for every
     actual cover map f : S1728CoverMap A B, defined as the S1742 2-Yoneda
     realisation of
       vcomp (vcomp (S1744BaseChange A).toSource f.map) (S1743Lift B);
   * S1744CanonicalModelHomActionActual : S1744CanonicalModelHomAction;
   * S1744RepresentableModelFunctoriality_holds :
       S1744RepresentableModelFunctoriality (Nonempty of the action type).

   This uses only unconditional inputs: the presentation from the finite-etale
   predicate and S1743's lift.  Axioms of S1744ModelMapOfCoverMap:
   propext, Classical.choice, Quot.sound.

## Exact reductions (kernel checked)

* S1744AffineCoverModelMissing_iff:
    S1733AffineCoverModelMissing
      <-> exists M : S1744ModelData,
            Nonempty (forall A B, (M.model A --> M.model B) = S1728CoverMap A B).
  Five of the six fields are discharged; the whole missing content is homEquiv.

* S1744ModelHomComparison_iff and S1744ModelHomComparison_iff_action:
    the homEquiv is equivalent to a comparison structure
    (homToModel, homToCover, two inverse laws), equivalently to an action plus
    bijectivity.

* S1744CanonicalModelHomEquiv_iff_action:
    S1744CanonicalModelHomEquiv <-> exists act : action, Bijective act.

* S1744CoverSliceEquivalence_iff:
    S1733CoverSliceEquivalence <-> exists F : S1728Cover --> S1733Slice,
      F.Faithful and F.Full and F.EssSurj.

* S1744Cover_nonempty_of_sliceEquivalence:
    S1733CoverSliceEquivalence -> Nonempty S1728Cover.  So the slice route can
    never be discharged by proving the cover type empty (the slice is nonempty
    and an equivalence is essentially surjective).

* S1744SmallRawCoverDataRequired_of_bijective (alias
  S1744SmallRawCoverDataRequired_of_residual) and
  S1744SmallRawCoverDataRequired_of_canonicalHomEquiv,
  S1744Category01_of_canonicalHomEquiv: bijectivity of the constructed action
  gives S1728SmallRawCoverDataRequired and Nonempty (Category.{0,1}) on the
  actual cover type (through S1733 and S1728).

## Residual lemma list

Direct route (S1733AffineCoverModel):

* R1a (2-Yoneda for representable etale pseudofunctors): DONE in S1742
  (tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean,
  S1742HomOfStrongTrans / S1742StrongTransOfHom /
  S1742TwoYoneda_comparison).
* R1b (functoriality of the canonical model): DONE here
  (S1744ModelMapOfCoverMap, S1744RepresentableModelFunctoriality_holds).
* R2 (bijectivity of the action): OPEN, and split into
  - S1744CanonicalModelHomActionInjective: doubtful for the canonical model.
    The action is built from the presentation at the identity point and the
    S1743 lift, so it cannot see information away from that point; two cover
    maps that differ only away from the base point should have the same model
    morphism.  The next theorem to attempt is therefore the *negative* one:
    the action is constant on cover maps related by 2-cells over the identity
    point.
  - S1744CanonicalModelHomActionSurjective: genuine finite-etale descent
    (a model morphism extends to a strong transformation of the etale stacks).
    Not derivable from the representability predicate: baseChange chooses one
    presentation per test scheme and point with no compatibility in the stack
    morphism, so presentations of different covers are unrelated, and the tree
    has no finite-etale descent.

Slice route (S1733CoverSliceEquivalence):

* S1: S1744SliceFunctorSpec (a faithful, full, essentially surjective functor
  S1728Cover --> S1733Slice).  Object part: DONE (S1744SliceObject).
  Morphism part: open, but the same construction as R1b applies
  (S1742 realisation of Y(model A) --> A.source --> B.source --> Y(model B));
  the three properties remain.

## Relation between the two S1733 missing statements

They are not inter-derivable in the present state.  The affine-cover route needs
an equivalence on the *raw* cover maps (Type 1), while the slice route compares
2-isomorphism classes: a slice equivalence supplies a Type 0 hom family for the
2-iso quotient, not for the raw maps, so it does not give
S1728SmallRawCoverDataRequired.  Conversely nothing in S1728SmallRawCoverData
gives object-level essential smallness.

## Dependency versions at verification time

* S1742TwoYonedaActual.lean SHA256
  13B06077D3D9C219D64611EB254F4F6C081469BEE00224349976BE1FD603D0B4
  (olean 2026-11-01 0:27:47, 177600 bytes).
* S1743CoverSliceActual.lean SHA256
  64E687F9F6C31583DD0A6D09AE73B848B5E21FCC5D888387A9489982711CE83F
  (olean 2026-11-01 0:36:58, 235728 bytes).
* S1733EssentiallySmallCoversActual.lean SHA256
  C98C82F95D1B013FFD2FF6F0CE7C3956603B59AF14DB2E30A244DB6C2A920E3C
  (olean 2026-11-01 0:04:05, 146480 bytes).

S1742 and S1743 are parallel packages; if their owners change these files, S1744
must be re-verified (lake env lean on the file, then rebuild its olean with -o).

## Reproduce

    cd D:/lean
    lake env lean tmp/sheaf/xif/paper/S1744Category01AssemblyActual.lean
    lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1744Category01AssemblyActual.olean tmp/sheaf/xif/paper/S1744Category01AssemblyActual.lean

Axiom audit: every #print axioms in the file reports only propext,
Classical.choice and Quot.sound; the string sorryAx does not occur in the output.
