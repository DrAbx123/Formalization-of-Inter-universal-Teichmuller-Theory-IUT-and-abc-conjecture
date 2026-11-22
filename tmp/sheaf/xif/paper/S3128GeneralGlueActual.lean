import tmp.sheaf.xif.paper.S3128GeneralCoequalizerTargetActual
import Mathlib.AlgebraicGeometry.Sites.Fpqc
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3128GeneralGlueActual
open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128AffineCoequalizerActual
open LeanFormal.IUT.XiFPaper.S3128GeneralCoequalizerTargetActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {G : Type} [Group G] {A : Type} [CommRing A] [MulSemiringAction G A]
/-- Actual affine-target specialization of the general coequalizer target. -/
theorem S3128GeneralCoequalizerTarget_affine (B : Type) [CommRing B] :
    S3128GeneralCoequalizerTarget G A (Spec (CommRingCat.of B)) := by
  intro u hu
  exact S3128AffineCoconeTarget_holds G A B u hu
/-- The descent compatibility for q: equal images under q have equal images under u.
Also the precise content needed by `EffectiveEpi.desc`. -/
def S3128DescentCompat
    (T : Scheme) (u : Spec (CommRingCat.of A) ⟶ T) : Prop :=
  ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of A)),
    g₁ ≫ S3128SpecQuotientMap (G := G) (A := A) =
      g₂ ≫ S3128SpecQuotientMap (G := G) (A := A) →
    g₁ ≫ u = g₂ ≫ u

/-- Actual fpqc/effective-epi descent: an invariant map satisfying descent
compatibility descends uniquely through the quotient map q. -/
theorem S3128GeneralCoequalizerTarget_of_effectiveEpi
    (T : Scheme) (u : Spec (CommRingCat.of A) ⟶ T)
    [EffectiveEpi (S3128SpecQuotientMap (G := G) (A := A))]
    (hcompat : S3128DescentCompat (G := G) (A := A) T u) :
    ∃! (v : Spec (CommRingCat.of (S3128FixedSubring G A)) ⟶ T),
      S3128SpecQuotientMap (G := G) (A := A) ≫ v = u := by
  let v := EffectiveEpi.desc (S3128SpecQuotientMap (G := G) (A := A)) u hcompat
  refine ⟨v, EffectiveEpi.fac _ u hcompat, ?_⟩
  intro w hw
  exact EffectiveEpi.uniq _ u hcompat w hw

/-- fpqc-cover form: if the quotient map is flat, surjective and quasi-compact
(hence an fpqc cover and an effective epimorphism), invariant maps satisfying
descent compatibility descend uniquely. -/
theorem S3128GeneralCoequalizerTarget_of_fpqc
    (T : Scheme) (u : Spec (CommRingCat.of A) ⟶ T)
    [Flat (S3128SpecQuotientMap (G := G) (A := A))]
    [Surjective (S3128SpecQuotientMap (G := G) (A := A))]
    [QuasiCompact (S3128SpecQuotientMap (G := G) (A := A))]
    (hcompat : S3128DescentCompat (G := G) (A := A) T u) :
    ∃! (v : Spec (CommRingCat.of (S3128FixedSubring G A)) ⟶ T),
      S3128SpecQuotientMap (G := G) (A := A) ≫ v = u := by
  haveI : EffectiveEpi (S3128SpecQuotientMap (G := G) (A := A)) := inferInstance
  exact S3128GeneralCoequalizerTarget_of_effectiveEpi T u hcompat

/-- The exact remaining general-target obligation. -/
def S3128GeneralCoequalizerTarget_gap (T : Scheme) : Prop :=
  S3128GeneralCoequalizerTarget G A T
/-- Generic Zariski gluing: compatible local maps glue uniquely. -/
theorem S3128_glue_cover {X T : Scheme} (𝒰 : X.OpenCover)
    (v : (i : 𝒰.I₀) → 𝒰.X i ⟶ T)
    (hv : ∀ (i j : 𝒰.I₀),
      Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ v i =
        Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ v j) :
    ∃! (w : X ⟶ T), ∀ i : 𝒰.I₀, 𝒰.f i ≫ w = v i := by
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 v hv, ?_, ?_⟩
  · intro i
    exact Scheme.Cover.ι_glueMorphisms 𝒰 v hv i
  · intro w hw
    apply Scheme.Cover.hom_ext 𝒰
    intro i
    rw [hw i]
    exact (Scheme.Cover.ι_glueMorphisms 𝒰 v hv i).symm

#check S3128_glue_cover
#check S3128GeneralCoequalizerTarget_of_fpqc
#check S3128DescentCompat
#check S3128GeneralCoequalizerTarget_of_effectiveEpi
#check S3128GeneralCoequalizerTarget_affine
#check S3128GeneralCoequalizerTarget_gap
end LeanFormal.IUT.XiFPaper.S3128GeneralGlueActual
end
