import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.EtaleCoverCategoryActual

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- The raw category structure on cover maps: Hom is the actual cover-map
type, identity and composition are S1641's actual constructions. -/
@[reducible] noncomputable def S3124CoverCategoryStruct :
    CategoryStruct (OrbicurveFiniteEtaleCover X) where
  Hom := OrbicurveFiniteEtaleCoverMap
  id := S1641CoverMapId
  comp := S1641CoverMapComp

/-- The target id_comp law for the raw structure. -/
def S3124IdCompLaw : Prop :=
  forall {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B),
    S1641CoverMapComp (S1641CoverMapId A) f = f

/-- The target comp_id law for the raw structure. -/
def S3124CompIdLaw : Prop :=
  forall {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B),
    S1641CoverMapComp f (S1641CoverMapId B) = f

/-- The target associativity law for the raw structure. -/
def S3124AssocLaw : Prop :=
  forall {A B C D : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (h : OrbicurveFiniteEtaleCoverMap C D),
    S1641CoverMapComp (S1641CoverMapComp f g) h =
      S1641CoverMapComp f (S1641CoverMapComp g h)

/-- The actual 2-isomorphism-quotient category on the cover type (S1728). -/
noncomputable instance S3124CoverCategory11 :
    Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) :=
  S1728CoverCategory11 (F := F) (X := X)

#check S3124CoverCategoryStruct
#check S3124IdCompLaw
#check S3124CompIdLaw
#check S3124AssocLaw
#check S3124CoverCategory11

end LeanFormal.IUT.XiFPaper.EtaleCoverCategoryActual
end