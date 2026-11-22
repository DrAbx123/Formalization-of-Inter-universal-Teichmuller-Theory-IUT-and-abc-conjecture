import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitFactorizationProvider

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1D1P3Actual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open scoped Classical

variable {V : Type*}

/-- Actual self Kummer layer from a strip and a factorization of the acting group
through the strip's local groups. -/
def selfKummerLayerOfFactorization {G : Type*} [Group G] [TopologicalSpace G]
    (S : FPrimeStrip V) (g : forall v : V, G →* S.toDPrimeStrip.Pi v) :
    SourceTimesMuKummerLayer G S S where
  sourceAction v := (S.unitsAction v).comp (g v)
  targetAction v := (S.unitsAction v).comp (g v)
  kummer v := TimesMuKummer.Isomorphism.refl ((S.unitsAction v).comp (g v))

/-- Actual self Kummer arrow from the same data. -/
def selfKummerArrowOfFactorization {G : Type*} [Group G] [TopologicalSpace G]
    (S : FPrimeStrip V) (g : forall v : V, G →* S.toDPrimeStrip.Pi v) :
    SourceKummerArrow G S S :=
  sourceKummerArrowOfLayer (FPrimeStripEquiv.refl S) (selfKummerLayerOfFactorization S g)

/-- Exact nontrivial-arrow interface: for distinct upper/lower strips an
actual layer requires the two kappa representatives over a common module. -/
structure NontrivialKummerLayerSource {G : Type*} [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) where
  layer : SourceTimesMuKummerLayer G upper lower

end LeanFormal.IUT.XiFPaper.Mzk1D1P3Actual
end
