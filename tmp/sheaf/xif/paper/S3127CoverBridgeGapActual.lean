import tmp.sheaf.xif.paper.S3127CoverMorphismActual
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
namespace LeanFormal.IUT.XiFPaper.S3127CoverBridgeGapActual
variable {l : PrimeGeFive}

/-- A cover whose source stack is representable by an actual chosen scheme. -/
def S3127SourceRepresentable
    (C : OrbicurveFiniteEtaleCover (S1536XF (l := l))) : Prop :=
  ∃ scheme : SchemeOverField (S1348K l),
    C.source = S3127Source (l := l) scheme

/-- Every cover in the image of S3127 is source-representable. -/
theorem S3127ToOrbicurveCover_source_representable
    (A : S3127Cover (l := l)) :
    S3127SourceRepresentable (S3127ToOrbicurveCover A) :=
  ⟨A.scheme, rfl⟩

/-- Exact essential-surjectivity target: every source-representable cover is
in the image of S3127. -/
def S3127EssentialSurjectiveOnRepresentable : Prop :=
  ∀ C : OrbicurveFiniteEtaleCover (S1536XF (l := l)),
    S3127SourceRepresentable C →
      ∃ A : S3127Cover (l := l), S3127ToOrbicurveCover A = C

/-- Obstruction: full essential surjectivity forces every cover source to be
representable.  Since `OrbicurveFiniteEtaleCover.source` is an arbitrary
`EtaleStackOverField`, this is the exact missing representability field. -/
theorem S3127_essSurj_implies_representable
    (h : S3127EssentialSurjectiveTarget (l := l)) :
    ∀ C : OrbicurveFiniteEtaleCover (S1536XF (l := l)),
      S3127SourceRepresentable C := by
  intro C
  obtain ⟨A, hA⟩ := h C
  refine ⟨A.scheme, ?_⟩
  rw [← hA]
  rfl

/-- Exact gap for using S3127Category directly as the cover category of
`OrbicurveEtaleFundamentalGroup`: its object type only represents covers with
representable source, and its Hom type is `S3127RepMap`, not an arbitrary
`OrbicurveEtaleFundamentalGroup.coverCategory`. -/
def S3127DirectCoverCategoryGap : Prop :=
  (∀ C : OrbicurveFiniteEtaleCover (S1536XF (l := l)),
      S3127SourceRepresentable C) ∧
    Nonempty (Category.{0, 1} (OrbicurveFiniteEtaleCover (S1536XF (l := l))))

#check S3127SourceRepresentable
#check S3127ToOrbicurveCover_source_representable
#check S3127EssentialSurjectiveOnRepresentable
#check S3127_essSurj_implies_representable
#check S3127DirectCoverCategoryGap
#print axioms S3127_essSurj_implies_representable

end LeanFormal.IUT.XiFPaper.S3127CoverBridgeGapActual