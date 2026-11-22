import tmp.sheaf.xif.paper.S3128AffineCoequalizerActual

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual

variable {G : Type} [Group G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B]

/-- Restriction of an equivariant ring map to fixed subrings. -/
noncomputable def S3128FixedSubringMap
    (φ : A →+* B) (hφ : forall (g : G) (a : A), φ (g • a) = g • φ a) :
    S3128FixedSubring G A →+* S3128FixedSubring G B :=
  RingHom.codRestrict (φ.comp (S3128FixedSubring G A).subtype)
    (S3128FixedSubring G B) (by
      intro a
      intro g
      rw [RingHom.comp_apply, ← hφ]
      congr 1
      exact a.property g)

/-- The fixed-subring map composed with the subtype is the original map. -/
theorem S3128FixedSubringMap_subtype
    (φ : A →+* B) (hφ : forall (g : G) (a : A), φ (g • a) = g • φ a) :
    (S3128FixedSubring G B).subtype.comp
        (S3128FixedSubringMap (G := G) (A := A) (B := B) φ hφ) =
      φ.comp (S3128FixedSubring G A).subtype := by
  apply RingHom.ext
  intro a
  simp [S3128FixedSubringMap]

/-- The map Spec (B^G) → Spec (A^G). -/
noncomputable def S3128SpecFixedMap
    (φ : A →+* B) (hφ : forall (g : G) (a : A), φ (g • a) = g • φ a) :
    Spec (CommRingCat.of (S3128FixedSubring G B)) ⟶
      Spec (CommRingCat.of (S3128FixedSubring G A)) :=
  Spec.map (CommRingCat.ofHom
    (S3128FixedSubringMap (G := G) (A := A) (B := B) φ hφ))

/-- Naturality square of quotient maps for an equivariant ring map. -/
theorem S3128SpecQuotientMap_natural
    (φ : A →+* B) (hφ : forall (g : G) (a : A), φ (g • a) = g • φ a) :
    Spec.map (CommRingCat.ofHom φ) ≫
        S3128SpecQuotientMap (G := G) (A := A) =
      S3128SpecQuotientMap (G := G) (A := B) ≫
        S3128SpecFixedMap (G := G) (A := A) (B := B) φ hφ := by
  dsimp [S3128SpecQuotientMap, S3128SpecFixedMap]
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp [S3128SpecFixedMap, S3128FixedSubringMap,
    S3128FixedSubringMap_subtype]

#check S3128FixedSubringMap
#check S3128FixedSubringMap_subtype
#check S3128SpecFixedMap
#check S3128SpecQuotientMap_natural

end LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual
end