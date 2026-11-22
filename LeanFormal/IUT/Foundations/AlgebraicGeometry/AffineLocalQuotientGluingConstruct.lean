import LeanFormal.IUT.Foundations.AlgebraicGeometry.FixedLocalizationAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.PermutationTorsorQuotient
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Cover.Open
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct

noncomputable section

universe u v

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient

/-- Production fixed localization: away localization of fixed points. -/
noncomputable def fixedPointLocalizationEquiv
    {A : Type u} {B : Type v} {G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Fintype G] [Algebra.IsInvariant A B G]
    (hinj : Function.Injective (algebraMap A B)) (f : A) :
    Localization.Away f ≃+*
      FixedPoints.subring (Localization.Away (algebraMap A B f)) G :=
  LeanFormal.N8.FixedLocalizationAction.awayFixedPointsEquiv (A := A) (B := B) (G := G)
    (f := f) hinj

/-- Absolute affine fixed-point quotient chart `Spec (A^G)`. -/
noncomputable def affineFixedPointChart (R A G : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Group G] [MulSemiringAction G A] [SMulCommClass G R A] : Scheme :=
  Spec (CommRingCat.of ↥(fixedPointSubalgebra R A G))

noncomputable def affineFixedPointChartMap (R A G : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Group G] [MulSemiringAction G A] [SMulCommClass G R A] :
    affineFixedPointChart R A G ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R A G)))

/-- Local pre-gluing data for affine quotient charts.  The fields are exactly the
gluing data of the local quotient schemes; `toSchemeGlueData` constructs the actual
`Scheme.GlueData` from them, rather than accepting it as a field. -/
structure AffineLocalQuotientPreglueData (S : Scheme.{u}) where
  J : Type u
  U : J → Scheme.{u}
  V : J × J → Scheme.{u}
  f : ∀ i j, V (i, j) ⟶ U i
  f_open : ∀ i j, IsOpenImmersion (f i j)
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k)
  f_id : ∀ i, IsIso (f i i)
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  t_id : ∀ i, t i i = 𝟙 _
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _
  q : ∀ i, U i ⟶ S
  q_etale : ∀ i, Etale (q i)

/-- The actual `Scheme.GlueData` constructed from affine local quotient pre-gluing
data.  This is not a field: the glue data is assembled from the local charts and
transition data. -/
noncomputable def AffineLocalQuotientPreglueData.toSchemeGlueData
    {S : Scheme.{u}} (P : AffineLocalQuotientPreglueData S) : Scheme.GlueData.{u} :=
  { toGlueData :=
      { J := P.J
        U := P.U
        V := P.V
        f := P.f
        f_mono := fun i j => by
          letI := P.f_open i j
          infer_instance
        f_hasPullback := P.f_hasPullback
        f_id := P.f_id
        t := P.t
        t_id := P.t_id
        t' := P.t'
        t_fac := P.t_fac
        cocycle := P.cocycle }
    f_open := P.f_open }

noncomputable def AffineLocalQuotientPreglueData.glued
    {S : Scheme.{u}} (P : AffineLocalQuotientPreglueData S) : Scheme.{u} :=
  P.toSchemeGlueData.glued

/-- The induced map from the glued scheme to the base, from the local quotient
charts.  Compatibility of the charts on the intersections is an explicit argument;
this is the actual colimit map, not a structure field. -/
noncomputable def AffineLocalQuotientPreglueData.gluedMapOfCompatible
    {S : Scheme.{u}} (P : AffineLocalQuotientPreglueData S)
    (hq : ∀ i j, pullback.fst ((P.toSchemeGlueData).ι i)
        ((P.toSchemeGlueData).ι j) ≫ P.q i =
        pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j) :
    P.toSchemeGlueData.glued ⟶ S :=
  let 𝒰 := (P.toSchemeGlueData).openCover
  𝒰.glueMorphisms P.q hq

theorem AffineLocalQuotientPreglueData.gluedMapOfCompatible_ι
    {S : Scheme.{u}} (P : AffineLocalQuotientPreglueData S)
    (hq : ∀ i j, pullback.fst ((P.toSchemeGlueData).ι i)
        ((P.toSchemeGlueData).ι j) ≫ P.q i =
        pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j)
    (i : P.J) :
    (P.toSchemeGlueData).ι i ≫ P.gluedMapOfCompatible hq = P.q i := by
  let 𝒰 := (P.toSchemeGlueData).openCover
  exact Scheme.Cover.ι_glueMorphisms 𝒰 P.q hq i

theorem AffineLocalQuotientPreglueData.gluedMapOfCompatible_etale
    {S : Scheme.{u}} (P : AffineLocalQuotientPreglueData S)
    (hq : ∀ i j, pullback.fst ((P.toSchemeGlueData).ι i)
        ((P.toSchemeGlueData).ι j) ≫ P.q i =
        pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j) :
    Etale (P.gluedMapOfCompatible hq) := by
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale)
    (P.toSchemeGlueData).openCover).mpr ?_
  intro i
  change Etale ((P.toSchemeGlueData).ι i ≫ P.gluedMapOfCompatible hq)
  rw [P.gluedMapOfCompatible_ι hq i]
  exact P.q_etale i


end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
