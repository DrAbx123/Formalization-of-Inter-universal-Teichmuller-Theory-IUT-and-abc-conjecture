import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1490OrbicurveFundamentalGroupActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT CategoryTheory
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1490OrbicurveFundamentalGroupActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3123GaloisComponentAudit

variable {l : PrimeGeFive}

/-- The actual cover type of S1536XF. -/
abbrev S3123Cover : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover (S1536XF (l := l))

/-- The actual 2-isomorphism-quotient category on the cover type. -/
noncomputable abbrev S3123CoverCategory11 : Category.{1, 1} S3123Cover :=
  S1728CoverCategory11 (F := S1348K l) (X := S1536XF (l := l))

/-- The target's small cover category type. -/
def S3123TargetCoverCategory : Type 1 :=
  Category.{0, 1} S3123Cover

/-- The target's Galois category type for a given cover category. -/
def S3123TargetGaloisCategory (C : S3123TargetCoverCategory (l := l)) : Prop :=
  @GaloisCategory.{1, 0} S3123Cover C

/-- First missing smallness datum: small raw cover-map carriers. -/
def S3123SmallRawCoverDataRequired : Prop :=
  S1728SmallRawCoverDataRequired (F := S1348K l) (X := S1536XF (l := l))

/-- Second missing datum: a small Galois model with fiber functor data. -/
abbrev S3123SmallGaloisModel : Type 1 :=
  S1728SmallGaloisModel (F := S1348K l) (X := S1536XF (l := l))

/-- The target etale fundamental group type. -/
def S3123EtalePiTarget (G : ProfiniteGrp) : Type 1 :=
  Iut.OrbicurveEtaleFundamentalGroup (S1536XF (l := l)) G

/-- A target etale-pi certificate forces the small raw cover data. -/
theorem S3123SmallRawRequiredOfEtalePi
    {G : ProfiniteGrp}
    (D : S3123EtalePiTarget (l := l) G) :
    S3123SmallRawCoverDataRequired (l := l) :=
  S1728SmallRawCoverDataOfEtalePi (F := S1348K l) (X := S1536XF (l := l)) D

/-- A small Galois model gives the required small cover category. -/
theorem S3123CoverCategoryOfSmallGaloisModel
    (M : S3123SmallGaloisModel (l := l)) :
    Nonempty (S3123TargetCoverCategory (l := l)) :=
  ⟨S1728ActualCategory01OfSmallGaloisModel M⟩

#check S3123Cover
#check S3123CoverCategory11
#check S3123TargetCoverCategory
#check S3123TargetGaloisCategory
#check S3123SmallRawCoverDataRequired
#check S3123SmallGaloisModel
#check S3123EtalePiTarget
#check S3123SmallRawRequiredOfEtalePi
#check S3123CoverCategoryOfSmallGaloisModel
#check S1490ArithmeticPiFirstMissing

end LeanFormal.IUT.XiFPaper.S3123GaloisComponentAudit
end