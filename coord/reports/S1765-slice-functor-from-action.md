# S1765: the slice functor from the S1744 action

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1765SliceFunctorFromActionActual.lean

EXIT=0 (lake env lean -o ..., no error, no warning, no sorryAx)

SHA256: 2BD072D6DE8846DF9162F45E5EE92BC42DDFEF60B9A10C5A5D4C33D0326033BD

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1765SliceFunctorFromActionActual.olean (241168 bytes)

Lines: 522.

## Verdict

The S1744 action does not by itself define a functor on the actual category
S1728ActualCategory11.  Unconditionally it is well defined on the source
2-isomorphism quotient, it is compatible with composition, and it is faithful.
Its identity law, however, is exactly the missing unit 2-cell
toSource vcomp lift = 1, i.e. S1756FirstMissing / S1743SourceRetraction.
This is the exact first missing.  It is a functor-coherence gap, not R2a/R2b:
R2a (raw injectivity) is not needed for faithfulness on the quotient, and R2b
is only the full/ess-surjectivity part of the comparison.
Conditional on S1756FirstMissing the functor is constructed.

## Constructed / proved unconditionally

* S1765Obj = S1744SliceObject (the required object map).
* S1765Eta: the S1744 action as a strong transformation.
* S1765EtaProjection: the action is compatible with the projections to
  Spec R' (the coherent cast needed for morphisms of the slice).
* S1765ModelMap_over: the action of every cover map is a morphism over
  Spec R', not merely over Spec K.
* S1765SliceHom / S1765SliceMap: the induced slice morphism.
* S1765SliceMap_congr: the slice morphism is constant on 2-isomorphism
  classes, hence descends to S1765Map on the homs of S1728ActualCategory11.
* S1765Map_mk: the defining formula on quotient representatives.
* S1765Map_comp: compatibility with categorical composition.
* S1765SliceHom_injective and S1765Map_injective: the action is faithful
  (equivalently, the quotient-level action is injective).
* S1765Map_id_of_firstMissing: conditional identity law.
* S1765Map_id_iff_firstMissing: the identity law is equivalent to
  S1756FirstMissing.
* S1765FunctorOfFirstMissing: the functor
  S1728Cover --> S1733Slice with object map S1765Obj and morphism map
  S1765Map, conditional on S1756FirstMissing.
* S1765FirstMissing_iff_retraction: S1756FirstMissing iff
  S1743SourceRetraction.
* S1765ActionSurjOnProjections_of_R2b: S1744's full R2b implies the
  restricted R2b needed for the slice functor.
* S1765EssSurj_iff: essential surjectivity of the conditional functor is
  exactly object-surjectivity S1765ObjectSurjective.

## Exact missing statements

1. Functor existence (the first missing): S1756FirstMissing,
   forall A, S1756End A = 1, equivalently the unit 2-cell
   toSource vcomp lift = 1 (S1756Unit), equivalently S1743SourceRetraction.
   This is the identity law of the action.

2. Fullness: S1765ActionSurjOnProjections, the surjectivity of the action
   onto model morphisms over Spec R'.  It is the restricted R2b; S1744's
   full R2b implies it.  Not proved.

3. Essential surjectivity: S1765ObjectSurjective.  Not proved.

Raw injectivity R2a is not required for the functor and is not proved.

## Axiom footprint

All #print axioms in the file report only propext, Classical.choice and
Quot.sound.  The string sorryAx does not occur in the output.  No sorry, no
new axiom, no Shrink/ULift/PUnit.

## Reproduce

    cd D:/lean
    lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1765SliceFunctorFromActionActual.olean tmp/sheaf/xif/paper/S1765SliceFunctorFromActionActual.lean

## Dependency versions at verification time

* S1744Category01AssemblyActual.lean SHA256
  0EC7647D9E64DF3852D6FE7207D92A2047AF385D56AE86338ABED42EF263224E
  (olean 235640 bytes, 2026-11-01 00:39:03).
* S1756CoverSourceRepresentabilityActual.lean SHA256
  BD710D363CFB460A94ED4449F6F01414A8315F67948D738EA4A20A76D3D80CEF
  (olean 250024 bytes, 2026-11-01 01:09:08).
* S1743CoverSliceActual.lean SHA256
  64E687F9F6C31583DD0A6D09AE73B848B5E21FCC5D888387A9489982711CE83F
  (olean 235728 bytes, 2026-11-01 00:36:58).
* S1742TwoYonedaActual.lean SHA256
  13B06077D3D9C219D64611EB254F4F6C081469BEE00224349976BE1FD603D0B4
  (olean 177600 bytes, 2026-11-01 00:27:47).

S1756 is a parallel package; if it changes, S1765 must be re-verified and its
olean rebuilt.
