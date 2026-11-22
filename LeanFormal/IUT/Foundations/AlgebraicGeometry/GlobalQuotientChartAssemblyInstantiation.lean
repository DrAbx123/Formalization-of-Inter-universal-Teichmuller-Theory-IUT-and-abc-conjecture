import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalGluedQuotientAssembly
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient chart assembly instantiation

This file instantiates the affine chart assembly from an actual finite etale
cover with finite group action and affine charts. The local affine quotient
charts are actual production covers; the only isolated input is the overlap
transition system, stated as an exact structure/obligation because the
scheme-level localization comparison is genuinely not available as a
field-free construction yet.

Post-compile-delta draft; held for the next batch. No provider or IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartAssemblyInstantiation

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalGluedQuotientAssembly
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Actual affine local quotient chart of a finite etale algebra with finite group action. -/
noncomputable def affineLocalQuotientChart
    (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  affineQuotientCoverGeneral (R := R) A G

/-- Actual chart map from the affine cover to its local quotient chart. -/
noncomputable def affineLocalQuotientChartMap
    (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    affineCover (R := R) A inferInstance inferInstance ⟶
      affineLocalQuotientChart (R := R) A G :=
  affineQuotientCoverMapGeneral (R := R) A G

theorem affineLocalQuotientChart_structureMap
    (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    (affineLocalQuotientChart (R := R) A G).structureMap =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (fixedPointSubalgebra R A G))) :=
  rfl

theorem affineLocalQuotientChart_etale
    (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    Etale (affineLocalQuotientChart (R := R) A G).structureMap :=
  (affineLocalQuotientChart (R := R) A G).etale_structureMap

theorem affineLocalQuotientChart_finite
    (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    IsFinite (affineLocalQuotientChart (R := R) A G).structureMap :=
  (affineLocalQuotientChart (R := R) A G).finite_structureMap

/-- Actual finite etale cover with a finite group action, as input for the
global quotient chart assembly. -/
structure FiniteEtaleCoverAction (S : Scheme.{u}) where
  X : FiniteEtaleCover S
  G : Type u
  groupG : Group G
  finiteG : Finite G
  act : letI := groupG; G →* CategoryTheory.Aut X

/-- A family of actual local quotient covers indexed by affine charts. -/
structure AffineChartFamilyData (S : Scheme.{u}) where
  J : Type u
  Q : J → FiniteEtaleCover S

namespace AffineChartFamilyData

variable (F : AffineChartFamilyData S)

/-- Chart maps of the local quotient family to the base. -/
noncomputable def q (i : F.J) : (F.Q i).carrier ⟶ S :=
  (F.Q i).structureMap

theorem q_etale (i : F.J) : Etale (F.q i) :=
  (F.Q i).etale_structureMap

theorem q_finite (i : F.J) : IsFinite (F.q i) :=
  (F.Q i).finite_structureMap

end AffineChartFamilyData

/-- Exact overlap transition data for a family of actual local quotient covers:
intersections, open-immersion projections, transitions, and cocycle. -/
structure AffineChartOverlapTransitionData {S : Scheme.{u}}
    (F : AffineChartFamilyData S) where
  /-- Intersection schemes. -/
  V : F.J × F.J → Scheme.{u}
  /-- Left projections. -/
  f : ∀ i j, V (i, j) ⟶ (F.Q i).carrier
  /-- Left projections are open immersions. -/
  f_open : ∀ i j, IsOpenImmersion (f i j)
  /-- Pullbacks of left projections exist. -/
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k)
  /-- Diagonal left projections are isomorphisms. -/
  f_id : ∀ i, IsIso (f i i)
  /-- Transitions. -/
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  /-- Diagonal transitions are identities. -/
  t_id : ∀ i, t i i = 𝟙 _
  /-- Triple-overlap transitions. -/
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  /-- Facet compatibility. -/
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  /-- Cocycle. -/
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

namespace AffineChartOverlapTransitionData

variable {S : Scheme.{u}} {F : AffineChartFamilyData S}
variable (T : AffineChartOverlapTransitionData F)

/-- The affine chart assembly obtained from the local quotient family and its
overlap transition data. -/
noncomputable def toChartAssembly : AffineGlobalQuotientChartAssembly S where
  J := F.J
  U i := (F.Q i).carrier
  V := T.V
  f := T.f
  f_open := T.f_open
  f_hasPullback := T.f_hasPullback
  f_id := T.f_id
  t := T.t
  t_id := T.t_id
  t' := T.t'
  t_fac := T.t_fac
  cocycle := T.cocycle
  q i := (F.Q i).structureMap
  q_etale i := (F.Q i).etale_structureMap

end AffineChartOverlapTransitionData

/-- Exact missing compatibility obligation: from an actual finite etale cover
with finite G action and affine charts, construct the local quotient family and
the scheme-level overlap transition data (with the fixed-localization
comparison as its missing ingredient). -/
def ChartAssemblyInstantiationObligation (S : Scheme.{u}) : Prop :=
  ∀ (A : FiniteEtaleCoverAction S) (J : Type u)
    (U : J → S.Opens), (∀ i, IsAffine (U i)) →
    ∃ F : AffineChartFamilyData S,
      Nonempty (AffineChartOverlapTransitionData F)

/-- Conditional assembly: the exact instantiation obligation gives a chart
assembly for every actual finite etale action and affine chart family. -/
theorem chartAssembly_of_instantiationObligation
    (h : ChartAssemblyInstantiationObligation S)
    (A : FiniteEtaleCoverAction S) (J : Type u) (U : J → S.Opens)
    (hU : ∀ i, IsAffine (U i)) :
    ∃ (F : AffineChartFamilyData S)
      (T : AffineChartOverlapTransitionData F),
      Nonempty (AffineGlobalQuotientChartAssembly S) :=
  by
    rcases h A J U hU with ⟨F, ⟨T⟩⟩
    exact ⟨F, T, ⟨T.toChartAssembly⟩⟩
end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartAssemblyInstantiation
end