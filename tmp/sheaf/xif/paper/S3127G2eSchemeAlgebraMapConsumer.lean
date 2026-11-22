import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeAlgebraMapConsumer

theorem S3127G2eScheme_hom_comp {R : Type} [CommRing R] (Y : Scheme)
    (alg : R →+* Scheme.Γ.obj (Opposite.op Y))
    (e : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y))
    (hfix : forall c : R, e (alg c) = alg c) :
    (S3127G2eScheme Y e).hom ≫
        Spec.map (CommRingCat.ofHom alg) =
      Spec.map (CommRingCat.ofHom alg) := by
  rw [S3127G2eScheme_hom, ← Spec.map_comp]
  congr 1
  ext c
  exact hfix c

#check S3127G2eScheme_hom_comp
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeAlgebraMapConsumer
end