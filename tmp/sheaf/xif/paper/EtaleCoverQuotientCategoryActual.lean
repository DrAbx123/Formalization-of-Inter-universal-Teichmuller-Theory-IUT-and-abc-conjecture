import tmp.sheaf.xif.paper.EtaleCoverCategoryActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1490OrbicurveFundamentalGroupActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.EtaleCoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.EtaleCoverQuotientCategoryActual

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- The quotient-category Hom type: 2-isomorphism classes of raw cover maps. -/
abbrev S3125Hom (A B : OrbicurveFiniteEtaleCover X) : Type (u + 1) :=
  S1728CoverMapClass (A := A) (B := B)

/-- The quotient map from raw cover maps to quotient-category morphisms. -/
noncomputable def S3125QuotMk {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) : A ⟶ B :=
  Quot.mk (fun f g : OrbicurveFiniteEtaleCoverMap A B => S1728CoverMapRel f g) f

/-- Exact bijectivity target for the quotient map; this is what the target's
coverMorphism_bijective would require if coverMorphism were Quot.mk. -/
def S3125QuotMkBijectiveTarget : Prop :=
  forall (A B : OrbicurveFiniteEtaleCover X),
    Function.Bijective (S3125QuotMk (A := A) (B := B))

/-- Alternative: every 2-isomorphism class of raw cover maps is a singleton. -/
def S3125SingletonClassesTarget : Prop :=
  forall {A B : OrbicurveFiniteEtaleCover X}
    (f g : OrbicurveFiniteEtaleCoverMap A B),
    S1728CoverMapRel f g -> f = g

/-- GaloisCategory target on the quotient category. -/
def S3125GaloisCategoryTarget : Prop :=
  @GaloisCategory.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X)
    (S1728CoverCategory11 (F := F) (X := X))

/-- The actual quotient Category instance. -/
noncomputable instance S3125CoverCategory :
    Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) :=
  S1728CoverCategory11 (F := F) (X := X)

#check S3125Hom
#check S3125QuotMk
#check S3125QuotMkBijectiveTarget
#check S3125SingletonClassesTarget
#check S3125GaloisCategoryTarget
#check S3125CoverCategory

end LeanFormal.IUT.XiFPaper.EtaleCoverQuotientCategoryActual
end