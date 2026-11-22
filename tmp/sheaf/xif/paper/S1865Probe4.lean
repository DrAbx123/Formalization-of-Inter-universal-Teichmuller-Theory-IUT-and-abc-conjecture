import tmp.sheaf.xif.paper.S1878CoherentAffineBridgeActual
import tmp.sheaf.xif.paper.S1854CoherentCategoryActual
import tmp.sheaf.xif.paper.S1857CoherentLimits01Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1865CoprodApexActual

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

attribute [local instance] S1854CoherentCategory11

noncomputable def S1865CoherentTo1854 :
    @CategoryTheory.Functor S1878CoherentCategory inferInstance
      CoherentCover S1854CoherentCategory11 where
  obj C := C
  map {C D} f := (S1854QuotEquiv C D).symm f.hom
  map_id C := by
    change (S1854QuotEquiv C C).symm (𝟙 (CoherentCover.cover C)) = S1857Id11 C
    rw [S1857Id11_def]
  map_comp {C D E} f g := by
    change (S1854QuotEquiv C E).symm (f.hom ≫ g.hom) =
      S1857Comp11 ((S1854QuotEquiv C D).symm f.hom)
        ((S1854QuotEquiv D E).symm g.hom)
    rw [S1857Comp11_def]
    congr 1
    simp only [Equiv.apply_symm_apply]

instance S1865CoherentTo1854_faithful : S1865CoherentTo1854.Faithful where
  map_injective {C D} f g h := by
    apply InducedCategory.hom_ext
    exact (S1854QuotEquiv C D).symm.injective h

instance S1865CoherentTo1854_full : S1865CoherentTo1854.Full where
  map_surjective {C D} (f : S1854CoherentQuot C D) :=
    ⟨InducedCategory.homMk (S1854QuotEquiv C D f), by
      change (S1854QuotEquiv C D).symm (S1854QuotEquiv C D f) = f
      exact Equiv.symm_apply_apply _ _⟩

instance S1865CoherentTo1854_essSurj : S1865CoherentTo1854.EssSurj where
  mem_essImage C := ⟨C, ⟨Iso.refl C⟩⟩

instance S1865CoherentTo1854_isEquivalence : S1865CoherentTo1854.IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
