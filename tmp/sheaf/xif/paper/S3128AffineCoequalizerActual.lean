import tmp.sheaf.xif.paper.S3128SpecActionActual
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128AffineCoequalizerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual

variable {G : Type} [Group G] {A B : Type}
  [CommRing A] [MulSemiringAction G A] [CommRing B]

/-- Affine coequalizer target: any invariant map B → A factors uniquely through A^G. -/
def S3128AffineCoequalizerTarget : Prop :=
  forall (f : B →+* A),
    (forall (b : B) (g : G), g • f b = f b) ->
      ∃! (v : Spec (CommRingCat.of (S3128FixedSubring G A)) ⟶
          Spec (CommRingCat.of B)),
        S3128SpecQuotientMap (G := G) (A := A) ≫ v =
          Spec.map (CommRingCat.ofHom f)

/-- Affine coequalizer universal property, ring-map form. -/
theorem S3128AffineCoequalizerTarget_holds :
    S3128AffineCoequalizerTarget (G := G) (A := A) (B := B) := by
  intro f hf
  obtain ⟨fbar, hfbar, huniq⟩ :=
    S3128FixedSubring_lift G A B f hf
  refine ⟨Spec.map (CommRingCat.ofHom fbar), ?_, ?_⟩
  · -- quotient map followed by Spec fbar equals Spec f
    dsimp [S3128SpecQuotientMap]
    rw [← Spec.map_comp]
    congr 1
    ext b
    exact congrArg (fun q : B →+* A => q b) hfbar
  · intro v hv
    -- uniqueness via Spec.preimage and fixed-subring lift uniqueness
    let g : CommRingCat.of B ⟶ CommRingCat.of (S3128FixedSubring G A) :=
      Spec.preimage v
    have hg : Spec.map g = v := Spec.map_preimage v
    have hcomp : Spec.map (g ≫ CommRingCat.ofHom
        (S3128FixedSubring G A).subtype) = Spec.map (CommRingCat.ofHom f) := by
      rw [Spec.map_comp, hg]
      simpa [S3128SpecQuotientMap] using hv
    have hgring : g ≫ CommRingCat.ofHom (S3128FixedSubring G A).subtype =
        CommRingCat.ofHom f := Spec.map_injective hcomp
    have hgfun : (S3128FixedSubring G A).subtype.comp g.hom = f := by
      ext b
      exact congrArg (fun q : CommRingCat.of B ⟶ CommRingCat.of A => q.hom b) hgring
    have hg' : g = CommRingCat.ofHom fbar := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      have h' := huniq (g.hom) hgfun
      exact congrArg (fun q : B →+* S3128FixedSubring G A => q b) h'
    show v = Spec.map (CommRingCat.ofHom fbar)
    rw [← hg, hg']


/-- Affine cocone target: every action-invariant map out of Spec A factors uniquely through Spec (A^G). -/
def S3128AffineCoconeTarget (G : Type) [Group G]
    (A : Type) [CommRing A] [MulSemiringAction G A]
    (B : Type) [CommRing B] : Prop :=
  forall (u : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)),
    (forall g : G, (S3128SpecAut (G := G) (A := A) g).hom ≫ u = u) ->
      ∃! (v : Spec (CommRingCat.of (S3128FixedSubring G A)) ⟶
          Spec (CommRingCat.of B)),
        S3128SpecQuotientMap (G := G) (A := A) ≫ v = u

/-- Affine cocone universal property. -/
theorem S3128AffineCoconeTarget_holds (G : Type) [Group G]
    (A : Type) [CommRing A] [MulSemiringAction G A]
    (B : Type) [CommRing B] :
    S3128AffineCoconeTarget G A B := by
  intro u hu
  let phi : CommRingCat.of B ⟶ CommRingCat.of A := Spec.preimage u
  let f : B →+* A := phi.hom
  have hf : forall (b : B) (g : G), g • f b = f b := by
    intro b g
    have hu' := hu g
    rw [← Spec.map_preimage u] at hu'
    dsimp [S3128SpecAut] at hu'
    rw [← Spec.map_comp] at hu'
    have hring := Spec.map_injective hu'
    have hfun := congrArg (fun q : CommRingCat.of B ⟶ CommRingCat.of A => q.hom b) hring
    have hval : (MulSemiringAction.toRingEquiv G A g) (f b) = f b := by
      simpa [phi, f, CommRingCat.comp_apply] using hfun
    exact (MulSemiringAction.toRingEquiv_apply_apply G A g (f b)).symm.trans hval
  obtain ⟨v, hv, huniq⟩ :=
    S3128AffineCoequalizerTarget_holds (G := G) (A := A) (B := B) f hf
  refine ⟨v, ?_, ?_⟩
  · have hmap : Spec.map (CommRingCat.ofHom f) = u := by
      simpa [phi, f] using Spec.map_preimage u
    change S3128SpecQuotientMap (G := G) (A := A) ≫ v = u
    rw [hv, hmap]
  · intro w hw
    apply huniq w
    have hmap : Spec.map (CommRingCat.ofHom f) = u := by
      simpa [phi, f] using Spec.map_preimage u
    change S3128SpecQuotientMap (G := G) (A := A) ≫ w =
      Spec.map (CommRingCat.ofHom f)
    rw [hmap]
    exact hw


#check S3128AffineCoconeTarget
#check S3128AffineCoconeTarget_holds
#check S3128AffineCoequalizerTarget
#check S3128AffineCoequalizerTarget_holds

end LeanFormal.IUT.XiFPaper.S3128AffineCoequalizerActual
end