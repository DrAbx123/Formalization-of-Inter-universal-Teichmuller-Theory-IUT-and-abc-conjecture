import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace Probe

variable {l : PrimeGeFive}

noncomputable def auto
    (σ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l) :
    S1419AffineOver (l := l) ⟶ S1419AffineOver (l := l) :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (S1348K l) (S1348CoordinateRing l))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (S1348K l) (S1348CoordinateRing l)))
    erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact σ.commutes x)


theorem auto_comp
    (σ τ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l) :
    auto σ ≫ auto τ = auto (τ.trans σ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom τ.toRingHom) =
    Spec.map (CommRingCat.ofHom (τ.trans σ).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl


#check auto
#check auto_comp

end Probe
end