# C9 no-sorry AffineQuotientCoconeIsColimit

Task: task-477. Date: 2026-10-25. Author: transport.
Target: LeanFormal/IUT/Foundations/AlgebraicGeometry/AffineQuotientCoconeIsColimit.lean
Compile: lean-serial -j1 -R D:/lean. No fake, axiom, or toy.

## 0. Result

The two real sorrys in the target file are removed:

1. quotientCocone: PROVED from the actual carrier projection invariance.
2. quotientCocone_isColimit: NOT proved; converted to an explicit residual
   type plus a conditional consumer, with the exact obstruction documented.

The file compiles EXIT=0.

## 1. Target file

- Path: LeanFormal/IUT/Foundations/AlgebraicGeometry/AffineQuotientCoconeIsColimit.lean
- lines: 123
- SHA256: 24DF854A1B989913EADD8E12AD0C8D51D6A9AFAA87286DC12BA0E2C687B511B3
- no actual sorry/axiom declarations: the only occurrences of the words are in
  the docstring stating their absence.

## 2. Compile

Command:

    Set-Location D:\lean
    pwsh -NoProfile -File tmp\n8-20261018\lead\lean-serial.ps1 env lean -j1 -R D:/lean LeanFormal/IUT/Foundations/AlgebraicGeometry/AffineQuotientCoconeIsColimit.lean

Result:

    EXIT=0
    no stdout/stderr errors

The target was edited because the task explicitly asks to replace provable
sorries. The edit is reported here. No other production file was modified.

## 3. What was proved

### 3.1 Elaboration repair

The original file did not elaborate its base/cover functor:

    abbrev base : Scheme.{u} := Spec (CommRingCat.of R)
    abbrev coverToScheme : FiniteEtaleCover base ⥤ Scheme.{u} := ...

R occurred only inside the body, not in the type, so the typeclass argument
CommRing R was left as a metavariable and Lean reported a stuck CommRing
instance. The repaired definitions make R explicit:

    abbrev base (R : Type u) [CommRing R] : Scheme.{u} := ...
    abbrev coverToScheme (R : Type u) [CommRing R] :
        FiniteEtaleCover (base R) ⥤ Scheme.{u} := ...

schemeActionFunctor uses coverToScheme R. This is a binding repair, not a
mathematical weakening.

### 3.2 actualCarrierProjection_invariant

Proved:

    theorem actualCarrierProjection_invariant (g : G) :
        (coverAutSchemeIso X act g).hom ≫ actualCarrierProjection X act =
          actualCarrierProjection X act

Proof uses the existing declarations:

- actualCarrierProjection_eq;
- coverSectionsSpecAut_agrees;
- the groupActionSpecAut identification
    (coverSectionsSpecAut X act g).hom
      = groupActionSpecAut (A := CoverCoordinateAlgebra X) (G := G) g^(-1)
  proved by unfolding and ext, exactly as in the existing
  quotientProjectionOfDiagram_invariant proof pattern;
- groupActionSpecAut_comp_affineFixedPointQuotientMap;
- the actual coordinate invariance actualCoordinateProjection_invariant.

No new axiom or toy object is introduced.

### 3.3 quotientCocone

Proved:

    noncomputable def quotientCocone :
        Cocone (schemeActionFunctor (R := R) X act)

The cocone point is the actual quotientScheme/actualQuotientScheme; the
component is actualCarrierProjection. Its naturality is exactly
actualCarrierProjection_invariant (after cases on the SingleObj homs).

This removes the first sorry.

## 4. Exact obstruction for IsColimit

The second sorry cannot be replaced by a proof from the current declarations.
It is replaced by:

    def quotientCoconeIsColimitResidual : Type _ :=
      IsColimit (quotientCocone (R := R) X act)

    noncomputable def quotientCocone_isColimit_of_residual
        (h : quotientCoconeIsColimitResidual X act) :
        IsColimit (quotientCocone (R := R) X act) := h

The exact obstruction is:

(E1) The existing universal property is affine-target only. The declaration
     actualCoordinateProjection_universal / coverCoordinateProjection_universal
     gives, for an affine target Spec B and an invariant map
     Spec (CoverCoordinateAlgebra X) -> Spec B, a unique factorization through
     actualQuotientScheme.

(E2) A scheme-level IsColimit of the action functor requires a desc map

         quotientScheme -> Z

     for an ARBITRARY cocone Z : Cocone (schemeActionFunctor X act), with
     arbitrary scheme Z, not only an affine target.

(E3) A morphism from the affine quotient scheme to an arbitrary scheme is not
     determined by its affine-target universal property. The affine-target
     factorization does not construct desc/fac/uniq for arbitrary Z.

(E4) There is no generic scheme-level categorical-quotient theorem in the
     imported declarations that would supply (E2) from the affine-target
     property. The target's own docstring says the scheme-level IsColimit is
     pending S1/S2 source records and is not the source-cover-category G2
     colimit.

(E5) No explicit scheme-level colimit provider or residual inhabitant exists in
     the current project. Adding one as an axiom would be a fake proof; adding
     a toy target category would change the statement. Both are excluded.

Thus the honest replacement is the residual type plus conditional consumer.
The residual is not a Prop that can be inhabited by a numerical or toy
argument; it is exactly the missing IsColimit statement.

## 5. API change

The original declaration

    noncomputable def quotientCocone_isColimit :
        IsColimit (quotientCocone ...)

was replaced by:

    def quotientCoconeIsColimitResidual : Type _
    noncomputable def quotientCocone_isColimit_of_residual
        (h : quotientCoconeIsColimitResidual X act) : IsColimit ...

No current consumer of quotientCocone_isColimit was found in the project
source; the replacement is therefore local to this candidate file. A future
S2 source record can populate the residual and immediately obtain the old
unconditional name.

## 6. Status

- quotientCocone: PROVED, no sorry.
- quotientCocone_isColimit: OPEN, explicit residual, no sorry/axiom/toy.
- target compiles EXIT=0.
- no other Lean/Project edits; only the named target file and this markdown.

target_accepted=false.
