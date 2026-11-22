import tmp.sheaf.xif.paper.S1522OrbicurveEtalePiActual
import Mathlib.CategoryTheory.Galois.Basic

-- S1529: reduce S1522 first missing Galois category to a Category instance
-- on the actual OrbicurveFiniteEtaleCover plus the actual Galois-category
-- inputs.  No group product/l-torsion/terminal substitute.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1529OrbicurveGaloisCategoryActual

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual

noncomputable abbrev S1529Orbicurve (l : PrimeGeFive) :
    Iut.HyperbolicOrbicurve (S1348K l) :=
  S1522Orbicurve l

abbrev S1529Cover (l : PrimeGeFive) : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover (S1529Orbicurve l)

/-- Exact first missing field: a Category instance on the actual represented
finite-etale cover type. -/
structure S1529CoverCategoryFirstMissing (l : PrimeGeFive) where
  coverCategory : Category.{0, 1} (S1529Cover l)

/-- Source G2 for a chosen cover category. -/
def S1529SourceG2 (l : PrimeGeFive) (C : Category.{0, 1} (S1529Cover l)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    @HasColimitsOfShape (SingleObj G) _ (S1529Cover l) C

/-- Remaining PreGaloisCategory inputs for a chosen cover category. -/
structure S1529OtherInputs (l : PrimeGeFive) (C : Category.{0, 1} (S1529Cover l)) where
  hasTerminal : @HasTerminal (S1529Cover l) C
  hasPullbacks : @HasPullbacks (S1529Cover l) C
  hasFiniteCoproducts : @HasFiniteCoproducts (S1529Cover l) C
  monoInducesIsoOnDirectSummand :
    ∀ {Y Z : S1529Cover l}
      (i : @Quiver.Hom _ C.toQuiver Y Z) [Mono i],
      ∃ (W : S1529Cover l) (u : @Quiver.Hom _ C.toQuiver W Z),
        Nonempty (IsColimit (BinaryCofan.mk i u))

/-- PreGaloisCategory from source G2 and the other inputs. -/
def S1529PreGaloisCategoryOfSourceG2
    (l : PrimeGeFive) (C : Category.{0, 1} (S1529Cover l))
    (hG2 : S1529SourceG2 l C) (h : S1529OtherInputs l C) :
    @PreGaloisCategory.{1, 0} (S1529Cover l) C :=
  { hasTerminal := h.hasTerminal
    hasPullbacks := h.hasPullbacks
    hasFiniteCoproducts := h.hasFiniteCoproducts
    hasQuotientsByFiniteGroups := fun G _ _ => hG2 G
    monoInducesIsoOnDirectSummand := h.monoInducesIsoOnDirectSummand }

/-- Full GaloisCategory from the cover category, G2, other inputs, and a
fiber functor. -/
def S1529GaloisCategoryOfInputs
    (l : PrimeGeFive) (C : Category.{0, 1} (S1529Cover l))
    (hG2 : S1529SourceG2 l C) (h : S1529OtherInputs l C)
    (hF : letI := S1529PreGaloisCategoryOfSourceG2 l C hG2 h;
      ∃ F : S1529Cover l ⥤ FintypeCat.{0},
        Nonempty (PreGaloisCategory.FiberFunctor F)) :
    @GaloisCategory.{1, 0} (S1529Cover l) C := by
  letI := S1529PreGaloisCategoryOfSourceG2 l C hG2 h
  exact
    { toPreGaloisCategory := S1529PreGaloisCategoryOfSourceG2 l C hG2 h
      hasFiberFunctor := hF }

/-- Remaining inputs for a supplied cover category. -/
structure S1529GaloisCategoryRemaining
    (l : PrimeGeFive) (C : Category.{0, 1} (S1529Cover l)) where
  sourceG2 : S1529SourceG2 l C
  otherInputs : S1529OtherInputs l C
  fiberFunctor :
    letI := S1529PreGaloisCategoryOfSourceG2 l C sourceG2 otherInputs;
    ∃ F : S1529Cover l ⥤ FintypeCat.{0},
      Nonempty (PreGaloisCategory.FiberFunctor F)

/-- Conditional actual construction of the S1522 GaloisCategory. -/
noncomputable def S1529GaloisCategory
    (l : PrimeGeFive) (C : S1529CoverCategoryFirstMissing l)
    (R : S1529GaloisCategoryRemaining l C.coverCategory) :
    @GaloisCategory.{1, 0} (S1529Cover l) C.coverCategory :=
  S1529GaloisCategoryOfInputs l C.coverCategory R.sourceG2
    R.otherInputs R.fiberFunctor

/-- Conditional assembly of the S1522 first missing structure. -/
noncomputable def S1529S1522FirstMissing
    (l : PrimeGeFive) (C : S1529CoverCategoryFirstMissing l)
    (R : S1529GaloisCategoryRemaining l C.coverCategory) :
    S1522GaloisCategoryFirstMissing l where
  coverCategory := C.coverCategory
  galoisCategory := S1529GaloisCategory l C R

/-- Exact first missing surface (no inhabitant asserted). -/
def S1529CoverCategoryRequired (l : PrimeGeFive) : Type 1 :=
  S1529CoverCategoryFirstMissing l

#check S1529Orbicurve
#check S1529Cover
#check S1529CoverCategoryFirstMissing
#check S1529SourceG2
#check S1529OtherInputs
#check S1529PreGaloisCategoryOfSourceG2
#check S1529GaloisCategoryOfInputs
#check S1529GaloisCategoryRemaining
#check S1529GaloisCategory
#check S1529S1522FirstMissing
#check S1529CoverCategoryRequired

end LeanFormal.IUT.XiFPaper.S1529OrbicurveGaloisCategoryActual

end