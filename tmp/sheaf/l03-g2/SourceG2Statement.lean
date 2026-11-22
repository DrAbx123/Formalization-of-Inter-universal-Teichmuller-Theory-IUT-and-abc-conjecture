import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Galois.Basic

/-!
# Source G2 statement (statement phase)

Exact source target: for a hyperbolic orbicurve `X`, a chosen category instance
`C` on its represented finite-etale covers, and every finite group `G`, the
category `C` has colimits of shape `SingleObj G`.

This file is statement-phase only.  The final declaration is a named `sorry`;
it does not assert a proof and does not touch production source.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace SHEAF.L03.SourceG2Statement

universe u

variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable [C : Category.{u} (Iut.OrbicurveFiniteEtaleCover X)]

/-- Exact source G2 statement: `C` has colimits of shape `SingleObj G` for every
finite group `G`, with the chosen category instance fixed explicitly. -/
def SourceG2 : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    @HasColimitsOfShape (SingleObj G) _ (Iut.OrbicurveFiniteEtaleCover X) C

/-- The source G2 hypothesis, unfolded to the exact `@HasColimitsOfShape` type. -/
theorem sourceG2_hasColimitsOfShape (hG2 : SourceG2 (X := X) (C := C))
    (G : Type u) [Group G] [Finite G] :
    @HasColimitsOfShape (SingleObj G) _ (Iut.OrbicurveFiniteEtaleCover X) C :=
  hG2 G

/-- Registration of the exact field used in `PreGaloisCategory`: the source G2
hypothesis is precisely the `hasQuotientsByFiniteGroups` field. -/
theorem sourceG2_fills_preGaloisCategory_hasQuotientsByFiniteGroups
    (hG2 : SourceG2 (X := X) (C := C)) :
    ∀ (G : Type u) [Group G] [Finite G],
      @HasColimitsOfShape (SingleObj G) _ (Iut.OrbicurveFiniteEtaleCover X) C :=
  sourceG2_hasColimitsOfShape (X := X) (C := C) hG2

/-- Inputs other than G2 needed to assemble a `GaloisCategory` on the cover
category: the remaining `PreGaloisCategory` fields and a fiber functor. -/
structure GaloisCategoryOtherInputs where
  hasTerminal : HasTerminal (Iut.OrbicurveFiniteEtaleCover X)
  hasPullbacks : HasPullbacks (Iut.OrbicurveFiniteEtaleCover X)
  hasFiniteCoproducts : HasFiniteCoproducts (Iut.OrbicurveFiniteEtaleCover X)
  monoInducesIsoOnDirectSummand :
    ∀ {Y Z : Iut.OrbicurveFiniteEtaleCover X} (i : Y ⟶ Z) [Mono i],
      ∃ (W : Iut.OrbicurveFiniteEtaleCover X) (u : W ⟶ Z),
        Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The source G2 field, plugged into the `PreGaloisCategory` structure. -/
def preGaloisCategoryOfSourceG2
    (hG2 : SourceG2 (X := X) (C := C)) (h : GaloisCategoryOtherInputs (X := X)) :
    @PreGaloisCategory (Iut.OrbicurveFiniteEtaleCover X) C :=
  { hasTerminal := h.hasTerminal
    hasPullbacks := h.hasPullbacks
    hasFiniteCoproducts := h.hasFiniteCoproducts
    hasQuotientsByFiniteGroups := fun G _ _ => hG2 G
    monoInducesIsoOnDirectSummand := h.monoInducesIsoOnDirectSummand }

/-- The full `GaloisCategory` structure on the cover category, with G2 supplied
by `SourceG2` and all other fields supplied by `GaloisCategoryOtherInputs`. -/
def galoisCategoryOfSourceG2
    (hG2 : SourceG2 (X := X) (C := C)) (h : GaloisCategoryOtherInputs (X := X))
    (hF : letI := preGaloisCategoryOfSourceG2 (X := X) (C := C) hG2 h;
      ∃ F : Iut.OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u},
        Nonempty (PreGaloisCategory.FiberFunctor F)) :
    @GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) C := by
  letI := preGaloisCategoryOfSourceG2 (X := X) (C := C) hG2 h
  exact
    { toPreGaloisCategory := preGaloisCategoryOfSourceG2 (X := X) (C := C) hG2 h
      hasFiberFunctor := hF }

end SHEAF.L03.SourceG2Statement