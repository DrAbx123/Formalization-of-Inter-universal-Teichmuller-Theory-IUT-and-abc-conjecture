import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartAssemblyInstantiation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart family from a global cover

This file constructs cover restrictions and local quotient charts over affine
opens. The local quotient is a cover of the affine open, not of the global
base; the latter is obtained only after gluing.

Post-compile-delta draft; held for the next batch. No provider or IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartAssemblyInstantiation
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Restriction of a finite etale cover to an open subscheme. -/
noncomputable def restrictCover (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] : FiniteEtaleCover U :=
  (FiniteEtaleCover.pullback (U.ι)).obj X

theorem restrictCover_structureMap (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] :
    (restrictCover X U).structureMap =
      Limits.pullback.snd X.structureMap (U.ι) :=
  FiniteEtaleCover.pullback_structureMap (g := (U.ι)) X

theorem restrictCover_etale (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] :
    Etale (restrictCover X U).structureMap :=
  (restrictCover X U).etale_structureMap

theorem restrictCover_finite (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] :
    IsFinite (restrictCover X U).structureMap :=
  (restrictCover X U).finite_structureMap

/-- The restriction is affine when the open is affine. -/
theorem restrictCover_isAffine (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] [IsAffine U] :
    IsAffine (restrictCover X U).carrier :=
  isAffine_of_isAffineHom (restrictCover X U).structureMap

/-- A local quotient chart over one affine open. -/
structure AffineChartLocalQuotient (S : Scheme.{u}) where
  U : S.Opens
  hU : IsAffine U
  XU : FiniteEtaleCover U
  hXU : IsAffine XU.carrier
  Q : FiniteEtaleCover U

namespace AffineChartLocalQuotient

variable (D : AffineChartLocalQuotient S)

/-- The chart map to the global base. -/
noncomputable def chartMap : D.Q.carrier ⟶ S :=
  D.Q.structureMap ≫ D.U.ι

theorem chartMap_etale : Etale D.chartMap :=
  Etale.comp D.Q.etale_structureMap (by infer_instance)

theorem chartMap_structureMap : D.chartMap = D.Q.structureMap ≫ D.U.ι :=
  rfl

end AffineChartLocalQuotient

/-- An affine chart family of local quotient covers, each over its affine open. -/
structure AffineChartLocalFamily (S : Scheme.{u}) where
  J : Type u
  chart : J → AffineChartLocalQuotient S

namespace AffineChartLocalFamily

variable (F : AffineChartLocalFamily S)

noncomputable def U (i : F.J) : S.Opens :=
  (F.chart i).U

noncomputable def Q (i : F.J) : FiniteEtaleCover (F.U i) :=
  (F.chart i).Q

noncomputable def chartMap (i : F.J) : (F.Q i).carrier ⟶ S :=
  (F.chart i).chartMap

theorem chartMap_etale (i : F.J) : Etale (F.chartMap i) :=
  (F.chart i).chartMap_etale

end AffineChartLocalFamily

/-- Exact construction target for the local quotient/action step. -/
def AffineChartLocalFamilyConstruction (S : Scheme.{u}) : Prop :=
  ∀ (X : FiniteEtaleCover S) (G : Type u) [Group G] [Finite G]
    (act : G →* CategoryTheory.Aut X)
    (J : Type u) (U : J → S.Opens) (hU : ∀ i, IsAffine (U i)),
    ∃ F : AffineChartLocalFamily S, ∀ i, (F.chart i).U = U i

namespace AffineChartLocalQuotient

variable (D : AffineChartLocalQuotient S)

theorem Q_etale : Etale D.Q.structureMap :=
  D.Q.etale_structureMap

theorem Q_finite : IsFinite D.Q.structureMap :=
  D.Q.finite_structureMap

theorem XU_etale : Etale D.XU.structureMap :=
  D.XU.etale_structureMap

theorem XU_finite : IsFinite D.XU.structureMap :=
  D.XU.finite_structureMap

theorem U_isAffine : IsAffine D.U :=
  D.hU

theorem XU_isAffine : IsAffine D.XU.carrier :=
  D.hXU

theorem chartMap_comp_structure :
    D.chartMap = D.Q.structureMap ≫ D.U.ι :=
  rfl

theorem chartMap_etale_assoc : Etale (D.Q.structureMap ≫ D.U.ι) :=
  D.chartMap_etale

end AffineChartLocalQuotient

namespace AffineChartLocalFamily

variable (F : AffineChartLocalFamily S)

theorem U_isAffine (i : F.J) : IsAffine (F.U i) :=
  (F.chart i).hU

theorem Q_etale (i : F.J) : Etale (F.Q i).structureMap :=
  (F.Q i).etale_structureMap

theorem Q_finite (i : F.J) : IsFinite (F.Q i).structureMap :=
  (F.Q i).finite_structureMap

theorem chartMap_eq (i : F.J) :
    F.chartMap i = (F.Q i).structureMap ≫ (F.U i).ι :=
  rfl

theorem chartMap_etale_assoc (i : F.J) :
    Etale ((F.Q i).structureMap ≫ (F.U i).ι) :=
  F.chartMap_etale i

end AffineChartLocalFamily

/-- Exact instantiation residual in local-quotient form. -/
def AffineChartLocalQuotientConstruction (S : Scheme.{u}) : Prop :=
  ∀ (X : FiniteEtaleCover S) (G : Type u) [Group G] [Finite G]
    (act : G →* CategoryTheory.Aut X)
    (U : S.Opens) (hU : IsAffine U) [Limits.HasPullbacksAlong (U.ι)],
    ∃ D : AffineChartLocalQuotient S,
      D.U = U ∧ D.XU = restrictCover X U

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
end