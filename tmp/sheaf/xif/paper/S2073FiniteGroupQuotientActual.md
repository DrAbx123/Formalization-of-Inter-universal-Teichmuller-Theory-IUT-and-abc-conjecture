# S2073: finite-group quotients of finite etale covers (first missing hasQuotientsByFiniteGroups)

**Status: missing** (Lean file compiles, EXIT=0; the quotient construction itself is not proved).

## Artifacts

| item | value |
|---|---|
| source | tmp/sheaf/xif/paper/S2073FiniteGroupQuotientActual.lean |
| source SHA256 | EAD91601F5DD57618BCD7320116D8DDE98E7C2C82AEF46E3F2758771CF295ACC |
| LEAN_EXIT | 0 |
| olean | .lake/build/lib/lean/tmp/sheaf/xif/paper/S2073FiniteGroupQuotientActual.olean |
| olean size | 429408 bytes |
| olean SHA256 | F021EEE3F6E526B6354726A71A1232AE1EA25BA867A09A78DDBCED62357B9EBB |
| axioms | propext, Classical.choice, Quot.sound (only) |

No sorry, admit, axiom, Nonempty gate or fabricated inhabitant.  Every declaration
listed in the file's axiom probes depends only on the three allowed axioms.

## 1. Mathlib inventory (v4.32.2)

Searched Mathlib/AlgebraicGeometry and Mathlib/CategoryTheory:

* **Scheme quotients by finite group actions: absent.**  No Scheme.Quotient, no GIT,
  no invariant subscheme, no quotient by a finite flat equivalence relation
  (SGA3 V.4), no group-scheme action theory.
* **Relative Spec of a quasi-coherent algebra sheaf: absent.**  Only Spec R for
  rings.  So the natural construction Y/G = Spec_X((f_* O_Y)^G) is not available.
* **Finite locally constant sheaves <-> finite etale schemes: absent.**  The
  Galois-category route (SGA1 V.4) is not available either.
* **PreGaloisCategory.hasQuotientsByFiniteGroups is a class field, not a theorem**
  (Mathlib/CategoryTheory/Galois/Basic.lean, line 74).  It cannot be instantiated
  for FiniteEtaleCover X without the construction itself.
* **Present and usable:** Etale/IsFinite stable under composition and base change
  and descending along fpqc/fppf (Morphisms/Etale.lean, Morphisms/Finite.lean,
  Morphisms/FlatDescent.lean, Morphisms/Descent.lean); affine schemes are
  Spec Gamma; the Gamma -| Spec adjunction (Spec.preimage/Spec.map).

## 2. What the project already has (imported, not reproved)

* FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale: A finite etale
  over R and G finite acting => A^G finite etale over R (no |G|-invertibility, no
  Noetherian, no local hypothesis).  This is the hard M2/M3 input and it is proved.
* AffineGeneralQuotientG2Consumer.affineQuotientCoverGeneral / _liftGeneral:
  the affine quotient cover Spec(A^G) -> Spec R as a FiniteEtaleCover, plus the
  affine-**target** universal property in cover form.
* AffineQuotientIntegration.affineQuotientUniversal (and
  AffineOverlapQuotientTransportProof.affineTargetUniversal): the affine-target
  universal property for invariant morphisms Spec A -> Spec B.
* AffineBaseFiniteEtaleQuotients.actionCoconeOfDiagram + quotientCoverOfDiagram +
  quotientProjectionOfDiagram(+_invariant): the quotient cocone for any
  F : SingleObj G ⥤ FiniteEtaleCover (Spec R).
* ClopenFiniteComplement.FiniteGroupQuotient.hasColimit_of_hasCoequalizer: a
  coequalizer of the action pair (∐_g Y, ∐_g Y) ⇒ Y gives the colimit.
* The repo also explicitly names the residual
  AffineOverlapQuotientTransportProof.NonAffineTargetExtensionResidual.

## 3. What S2073 proves (genuine, unconditional)

1. S2073CoconeOf: a cocone over ρ : SingleObj G ⥤ C is determined by the
   component at the unique object; naturality = invariance.
2. S2073QuotientData: Type-valued quotient datum (Q, q, invariance, desc, fac,
   uniq).  S2073QuotientData.isColimit: quotient data is a colimit cocone.
3. S2073quotientDataOfHasColimit: conversely every colimit gives quotient data.
4. S2073hasColimitsOfShape_of_quotientData and its converse
   S2073quotientData_of_hasColimitsOfShape: the card field
   Limits.HasColimitsOfShape (SingleObj G) (FiniteEtaleCover X) is *exactly* the
   existence of the quotient objects with their universal property.
5. S2073affineQuotientCover_etale / _finite: the affine quotient cover's
   structure map is Etale and IsFinite (Etale/IsFinite preservation), and
   S2073affineQuotientCover_lift: the affine-target universal property in cover form.
6. S2073curveScheme_eq_spec_coordinateRing and S2073curveHasQuotients_of_affine:
   the curve card's remaining field follows from the affine-base statement at
   R = curveCoordinateRing K.  Since the source curve is affine, the affine case
   is exactly what the curve card needs (no general-scheme gluing required).

## 4. Exact first missing statement

**S2073-M1 (affine base), named S2073AffineActionCoconeIsColimit R:**
for every commutative ring R and every F : SingleObj G ⥤ FiniteEtaleCover (Spec R),
   IsColimit (AffineBaseFiniteEtaleQuotients.actionCoconeOfDiagram F).cocone.

This is the precise gap: the existing affine universal property is stated for
affine targets Spec B, while a colimit in FiniteEtaleCover (Spec R) needs the
factorization for every finite etale cover target T, and T is only isomorphic to
Spec Γ(T).  The missing lemma is the transport of the affine-target universal
property through T.carrier.isoSpec and the Over-compatibility of the resulting
map of covers.

**S2073-M2 (arbitrary base), named S2073GlobalActionCoconeIsColimit S:**
the affine quotient data glue Zariski-locally on S and the glued cocone is a
colimit.  The repo's AffineLocalQuotientPreglueData / GlobalGluedQuotientData
files are the partial infrastructure; the assembly is not present.

Both are Type-valued structures with data fields (no Nonempty gate).  The file
proves: M1 => card field over Spec R (S2073affineHasQuotients_of_coconeIsColimit);
M2 => card field for S (S2073hasQuotients_of_globalCoconeIsColimit);
M1 at R = curveCoordinateRing K => the frozen curve card
(S2073curveRemainingFields_of_affine).

## 5. Minimal required API

Shortest path to close the curve card (X = curveScheme K is affine, so M2 is not
needed for the source curve):

1. Transport lemma: for T : FiniteEtaleCover (Spec R), the map
   (Y ⟶ T) -> (Spec Γ(Y) ⟶ Spec Γ(T)), f ↦ isoSpec.inv ≫ f.left ≫ isoSpec.hom,
   is injective (immediate from iso cancellation), and a cocone leg
   f : Y ⟶ T invariant under F.map g gives an invariant map
   f'' : Spec Γ(Y) ⟶ Spec Γ(T) for the section-ring action.
   Needs: CoverSectionsAction.coverSectionsSpecAut_agrees,
   coverAutSchemeIso_action_hom, and the g/g-inverse bookkeeping between
   MulSemiringAction.toRingEquiv and coverSectionsRingEquiv.
2. Apply the already-proved affine-target universal property
   (affineTargetUniversal / affineQuotientUniversal) to f''.
3. Build the map of covers Q ⟶ T from Spec.preimage of the resulting map; the
   Over-compatibility follows because Spec.preimage f'' is R-linear
   (from T.structureMap = isoSpec.hom ≫ Spec.map (algebraMap R Γ T)).
4. Uniqueness by Spec.map_injective + injectivity of A^G ↪ A + cover hom extensionality.

If instead one wants the Mathlib-free route for arbitrary X, the missing items are
relative Spec of the invariants sheaf plus Zariski gluing (SGA3 V.4 style).

## 6. Next executable step

Prove M1 by (1)-(4) above inside a new file importing
AffineBaseFiniteEtaleQuotients + AffineOverlapQuotientTransportProof, then replace
S2073AffineActionCoconeIsColimit by its inhabitant and instantiate
S2073curveRemainingFields_of_affine at K = ℚ_[v.1].
