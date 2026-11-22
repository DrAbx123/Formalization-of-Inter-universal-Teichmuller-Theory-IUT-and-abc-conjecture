# S1799 — affine finite-étale comparison for an arbitrary commutative ring

File: tmp/sheaf/xif/paper/S1799AffineFiniteEtaleEquivActual.lean

## Evidence

- EXIT = 0 (lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1799AffineFiniteEtaleEquivActual.olean).
- Source: 593 lines, 27004 bytes, SHA256 5338C34F729B23245520D59BD27C2409C9ACB3EDB57FA71BA349980BCD97B75C.
- Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1799AffineFiniteEtaleEquivActual.olean,
  671808 bytes, SHA256 BF86B1205E31920F74E3351A125902374CEB1D49858F748A3AA0D04A8957D251.
- Axiom audit of every main declaration (printed at the end of the file): only
  propext, Classical.choice, Quot.sound.  No sorry, admit, axiom, native_decide,
  Shrink, ULift or PUnit anywhere in the file.

## Statement

For an arbitrary CommRing R, with specBase R = Spec (CommRingCat.of R):

- algToCover : (CommAlgCat.FiniteEtale R)^op ⥤ FiniteEtaleCover (specBase R),
  A ↦ (Spec A ⟶ Spec R).
- coverToAlg : FiniteEtaleCover (specBase R) ⥤ (CommAlgCat.FiniteEtale R)^op,
  (X ⟶ Spec R) ↦ Γ(X, ⊤) with the R-algebra structure induced by the structure map.

Both are proved equivalences of categories:

- algToCover_isEquivalence / affineFiniteEtaleEquivalence :
    (CommAlgCat.FiniteEtale R)^op ≌ FiniteEtaleCover (specBase R).
- coverToAlg_isEquivalence / affineFiniteEtaleEquivalenceCoverFirst :
    FiniteEtaleCover (specBase R) ≌ (CommAlgCat.FiniteEtale R)^op.

and both comparison natural isomorphisms are proved:

- unitIso   : 𝟭 (CommAlgCat.FiniteEtale R)^op ≅ algToCover ⋙ coverToAlg
              (component Γ(Spec A) → A is Scheme.ΓSpecIso, naturality is
               Scheme.ΓSpecIso_naturality).
- counitIso : coverToAlg ⋙ algToCover ≅ 𝟭 (FiniteEtaleCover (specBase R))
              (component is Scheme.isoSpec.inv, naturality is
               Scheme.isoSpec_inv_naturality).

## Main lemmas

### Forward direction (algebra to cover)

- finiteEtaleStructureMap_etale : Etale (Spec.map (CommRingCat.ofHom (algebraMap R A.obj)))
  from HasRingHomProperty.Spec_iff and RingHom.etale_algebraMap.
- finiteEtaleStructureMap_finite : IsFinite of the same map, from
  IsFinite.SpecMap_iff and RingHom.finite_algebraMap.
- algToCover_full / algToCover_faithful : via Spec.fullyFaithful and Over.
- algToCover_essSurj :

### Backward direction (cover to algebra)

- finiteEtaleCover_carrier_isAffine : a finite morphism to an affine scheme has
  affine source (isAffine_of_isAffineHom), so every finite etale cover of Spec R
  is affine.
- coverSectionsFiniteEtale : Γ(X, ⊤) is a finite etale R-algebra:
  finite from Scheme.Hom.finite_appTop and Module.Finite.trans;
  etale from HasRingHomProperty.iff_of_isAffine and Algebra.Etale.comp.
- coverToAlg_map_apply / sectionsAlgHom : functoriality on morphisms of covers.
- coverToAlg_essSurj : X ≅ Spec Γ(X, ⊤) via Scheme.isoSpec.

## Mathlib boundary: no missing theorem

Mathlib 4.32.2 does not state the affine comparison itself, but every ingredient is
present and the whole comparison is derivable.  The exact Mathlib inputs used:

- AlgebraicGeometry.Scheme.isoSpec, Scheme.isoSpec_hom_naturality,
  Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_inv
  (AffineScheme.lean), IsAffine, isAffine_of_isAffineHom, isAffine_Spec.
- AlgebraicGeometry.Scheme.ΓSpecIso, Scheme.ΓSpecIso_naturality,
  Scheme.ΓSpecIso_inv_naturality, Scheme.SpecMap_ΓSpecIso_hom.
- HasRingHomProperty.Spec_iff, HasRingHomProperty.iff_of_isAffine,
  IsFinite.SpecMap_iff, Scheme.Hom.finite_appTop.
- RingHom.etale_algebraMap, RingHom.finite_algebraMap.
- CommAlgCat.FiniteEtale and its instances (RingTheory/Etale/Finite.lean), which
  are stated for an arbitrary CommRing.

Conversely, the earlier project files claimed the general case is missing only
because only the field case had been ported; the field-case proofs in
Example36SpecCoverFunctor / SpecCoverFullEquivalence / SpecCoverEquivalenceFinal /
SpecEssentialSurjectivity never use the field hypothesis, and this file is the
verbatim general-R port together with the explicit global-sections functor and its
natural isomorphisms.

## Consumers

- S1760's frozen structure S1760AffineCoverAlgebraEquivalence R has exactly the
  field type FiniteEtaleCover (Spec (CommRingCat.of R)) ≌ (CommAlgCat.FiniteEtale R)^op,
  which is the type of affineFiniteEtaleEquivalenceCoverFirst R; hence that structure
  is now inhabited (given the import).  Its conditional
  S1760AffineFunctionFieldFunctor / S1760AffineFunctionFieldEquivalence can therefore
  be instantiated unconditionally.
- S1779's S1779FirstMissing additionally requires the identification of the small
  cover category S1728Cover with FiniteEtaleCover (Spec R') and the hom comparison
  S1744 R2; this file supplies the affine equivalence half at the level of
  FiniteEtaleCover (Spec R') but does not identify S1728Cover with it.

## Honest boundary

- The two equivalences and both natural isomorphisms are proved, kernel checked.
- The single statement NOT proved is S1799TriangleIdentity, the triangle identity
  which packs unitIso and counitIso into one CategoryTheory.Equivalence record:
    (algToCover R).map ((unitIso R).hom.app X) ≫ (counitIso R).hom.app ((algToCover R).obj X)
      = 𝟙 ((algToCover R).obj X).
  Mathematically it is Spec.map (ΓSpecIso A).hom ≫ (Spec A).isoSpec.inv = 𝟙, i.e.
  Scheme.isoSpec_Spec_inv plus functoriality of Spec; the residual work is the
  definitional identification of the underlying ring map of the unit with
  (Scheme.ΓSpecIso A).hom across the ObjectProperty.FullSubcategory coercion
  (the InducedCategory/FullSubcategory defeq is not available at instances
  transparency).  No mathematical input is missing.  The two equivalences above do
  not depend on it.
