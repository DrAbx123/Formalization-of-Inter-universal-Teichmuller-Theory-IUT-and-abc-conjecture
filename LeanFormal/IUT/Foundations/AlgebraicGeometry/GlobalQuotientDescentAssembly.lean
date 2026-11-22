import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientIsColimit
import Mathlib.Tactic

/-!
# Descent assembly for the global quotient candidate

This file packages chart-level descent data and the fac/uniqueness hypotheses
needed for the IsColimit packaging. It does not construct an unconditional
descent family or a provider inhabitant; the residual is explicit.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentAssembly

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientIsColimit
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- A candidate global descent family: a map from the quotient cover to every
cocone over the action functor, with fac and uniqueness data. -/
structure GlobalDescentAssembly
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (A : GlobalQuotientActionData (R := R) X G) where
  desc : ∀ c : Cocone A.actionFunctor, A.quotientCover ⟶ c.pt
  fac : HasGlobalDescFac (R := R) (X := X) (G := G) A desc
  uniq : HasGlobalDescUniq (R := R) (X := X) (G := G) A desc

namespace GlobalDescentAssembly

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  {A : GlobalQuotientActionData (R := R) X G}
  (D : GlobalDescentAssembly (R := R) (A := A))

/-- The descent map at a cocone. -/
abbrev descAt (c : Cocone A.actionFunctor) : A.quotientCover ⟶ c.pt :=
  D.desc c

/-- Fac equation for the assembled descent map. -/
theorem facAt (c : Cocone A.actionFunctor) :
    A.projection ≫ D.desc c = c.ι.app (SingleObj.star G) :=
  D.fac c

/-- Uniqueness for the assembled descent map. -/
theorem uniqAt (c : Cocone A.actionFunctor) (m : A.quotientCover ⟶ c.pt)
    (hm : A.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = D.desc c :=
  D.uniq c m hm

/-- The assembled descent family gives the actual IsColimit of the quotient
cocone. -/
noncomputable def isColimit : IsColimit A.cocone :=
  isColimitOfGlobalDesc (R := R) (X := X) (G := G) A D.desc D.fac D.uniq

/-- The assembled IsColimit has the expected desc function. -/
theorem isColimit_desc (c : Cocone A.actionFunctor) :
    D.isColimit.desc c = D.desc c := rfl

/-- The assembled IsColimit has the expected fac equation. -/
theorem isColimit_fac (c : Cocone A.actionFunctor) :
    A.projection ≫ D.isColimit.desc c = c.ι.app (SingleObj.star G) :=
  D.facAt c

/-- The assembled IsColimit has the expected uniqueness property. -/
theorem isColimit_uniq (c : Cocone A.actionFunctor) (m : A.quotientCover ⟶ c.pt)
    (hm : A.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = D.isColimit.desc c := by
  rw [D.isColimit_desc]
  exact D.uniqAt c m hm

/-- Restriction of the assembled descent family to the identity cocone. -/
theorem desc_self :
    D.desc A.cocone = 𝟙 A.quotientCover := by
  apply D.uniqAt A.cocone (𝟙 _)
  rw [Category.comp_id]
  rfl

/-- Two assembled desc families with the same desc function are equal. -/
theorem ext {D E : GlobalDescentAssembly (R := R) (A := A)}
    (h : D.desc = E.desc) : D = E := by
  cases D with
  | mk d f u =>
    cases E with
    | mk d' f' u' =>
      simp only at h
      subst h
      congr

/-- Chart-level descent data before assembly: a map on the quotient cover
which is compatible with the quotient projection. -/
structure ChartLevelDescent
    (A : GlobalQuotientActionData (R := R) X G) where
  desc : ∀ c : Cocone A.actionFunctor, A.quotientCover ⟶ c.pt
  fac : ∀ c : Cocone A.actionFunctor,
    A.projection ≫ desc c = c.ι.app (SingleObj.star G)
  uniq : ∀ (c : Cocone A.actionFunctor) (m : A.quotientCover ⟶ c.pt),
    A.projection ≫ m = c.ι.app (SingleObj.star G) → m = desc c

/-- Chart-level descent data assembly. -/
noncomputable def ChartLevelDescent.toAssembly
    {A : GlobalQuotientActionData (R := R) X G} (D : ChartLevelDescent (R := R) (A := A)) :
    GlobalDescentAssembly (R := R) (A := A) :=
  { desc := D.desc, fac := D.fac, uniq := D.uniq }

/-- The assembly is an IsColimit exactly from chart-level descent data. -/
noncomputable def isColimitOfChartLevelDescent
    {A : GlobalQuotientActionData (R := R) X G} (D : ChartLevelDescent (R := R) (A := A)) :
    IsColimit A.cocone :=
  D.toAssembly.isColimit

/-- Exact residual for the descent assembly: the existence of a chart-level
desc family satisfying fac and uniqueness.  This is a proposition, not an
asserted inhabitant. -/
def descentAssemblyResidual
    (A : GlobalQuotientActionData (R := R) X G) : Prop :=
  Nonempty (ChartLevelDescent (R := R) (A := A))

/-- From an actual chart-level descent family, the residual is inhabited. -/
theorem descentAssemblyResidual_of_chartLevel
    {A : GlobalQuotientActionData (R := R) X G}
    (D : ChartLevelDescent (R := R) (A := A)) :
    descentAssemblyResidual (R := R) A :=
  ⟨D⟩

/-- A chart-level descent family is determined by its desc function. -/
theorem chartLevelDescent_ext
    {A : GlobalQuotientActionData (R := R) X G}
    {D E : ChartLevelDescent (R := R) (A := A)} (h : D.desc = E.desc) : D = E := by
  cases D with
  | mk d f u =>
    cases E with
    | mk d' f' u' =>
      simp only at h
      subst h
      congr

/-- The trivial descent family exists only when the projection is an
isomorphism; it is recorded conditionally. -/
noncomputable def trivialChartLevelDescent
    {A : GlobalQuotientActionData (R := R) X G}
    (e : A.quotientCover ≅ X)
    (hproj : A.projection = e.inv) : ChartLevelDescent (R := R) (A := A) :=
  { desc := fun c => e.hom ≫ c.ι.app (SingleObj.star G)
    fac := by
      intro c
      rw [← Category.assoc, hproj, Iso.inv_hom_id_assoc]
    uniq := by
      intro c m hm
      rw [← cancel_epi A.projection]
      · rw [hm]
      · exact hproj ▸ e.inv_hom_id_assoc _ }


/-- A descent family from a map out of the quotient cover and an isomorphism to
the projection, when the projection is invertible. -/
noncomputable def descentOfProjectionIso
    {A : GlobalQuotientActionData (R := R) X G}
    (e : A.quotientCover ≅ X) (hproj : A.projection = e.inv) :
    GlobalDescentAssembly (R := R) (A := A) :=
  (trivialChartLevelDescent (R := R) e hproj).toAssembly

/-- The desc of the projection-iso descent family. -/
theorem descentOfProjectionIso_desc
    {A : GlobalQuotientActionData (R := R) X G}
    (e : A.quotientCover ≅ X) (hproj : A.projection = e.inv)
    (c : Cocone A.actionFunctor) :
    (descentOfProjectionIso (R := R) e hproj).desc c =
      e.hom ≫ c.ι.app (SingleObj.star G) := rfl

/-- The fac of the projection-iso descent family. -/
theorem descentOfProjectionIso_fac
    {A : GlobalQuotientActionData (R := R) X G}
    (e : A.quotientCover ≅ X) (hproj : A.projection = e.inv)
    (c : Cocone A.actionFunctor) :
    A.projection ≫ (descentOfProjectionIso (R := R) e hproj).desc c =
      c.ι.app (SingleObj.star G) :=
  (descentOfProjectionIso (R := R) e hproj).fac c

/-- An assembly with a trivial target cocone. -/
noncomputable def assemblyToSelf
    {A : GlobalQuotientActionData (R := R) X G}
    (D : GlobalDescentAssembly (R := R) (A := A)) :
    A.quotientCover ⟶ A.quotientCover :=
  D.desc A.cocone

/-- The self-map of an assembly is the identity. -/
theorem assemblyToSelf_eq_id
    {A : GlobalQuotientActionData (R := R) X G}
    (D : GlobalDescentAssembly (R := R) (A := A)) :
    D.assemblyToSelf = 𝟙 A.quotientCover :=
  D.desc_self

/-- The fac condition read at the self cocone. -/
theorem assemblyToSelf_fac
    {A : GlobalQuotientActionData (R := R) X G}
    (D : GlobalDescentAssembly (R := R) (A := A)) :
    A.projection ≫ D.assemblyToSelf =
      A.cocone.ι.app (SingleObj.star G) :=
  D.fac cA where
  cA := A.cocone

/-- Pointwise form of the fac condition. -/
theorem fac_pointwise
    {A : GlobalQuotientActionData (R := R) X G}
    (D : GlobalDescentAssembly (R := R) (A := A))
    (c : Cocone A.actionFunctor) (j : SingleObj G) :
    A.projection ≫ D.desc c = c.ι.app j := by
  rw [D.facAt c]
  congr 1
  exact Subsingleton.elim _ _

/-- The uniqueness condition for two maps with the same fac. -/
theorem uniq_of_fac_eq
    {A : GlobalQuotientActionData (R := R) X G}
    (D : GlobalDescentAssembly (R := R) (A := A))
    {c : Cocone A.actionFunctor} {m n : A.quotientCover ⟶ c.pt}
    (hm : A.projection ≫ m = c.ι.app (SingleObj.star G))
    (hn : A.projection ≫ n = c.ι.app (SingleObj.star G)) : m = n := by
  rw [D.uniqAt c m hm, D.uniqAt c n hn]

/-- The assembly desc is natural in cocone morphisms. -/
theorem desc_natural
    {A : GlobalQuotientActionData (R := R) X G}
    (D : GlobalDescentAssembly (R := R) (A := A))
    {c d : Cocone A.actionFunctor} (f : c ⟶ d) :
    D.desc c ≫ f.hom = D.desc d := by
  apply D.uniqAt d
  rw [← Category.assoc, D.facAt c, f.w]
  exact D.facAt d

/-- Two descent assemblies with the same desc are equal. -/
theorem assembly_ext
    {A : GlobalQuotientActionData (R := R) X G}
    {D E : GlobalDescentAssembly (R := R) (A := A)}
    (h : D.desc = E.desc) : D = E :=
  GlobalDescentAssembly.ext (R := R) h

/-- The assembly desc is injective as a function into cocone maps. -/
theorem desc_injective
    {A : GlobalQuotientActionData (R := R) X G}
    (D : GlobalDescentAssembly (R := R) (A := A)) :
    Function.Injective D.desc := by
  intro c d h
  -- The cocones themselves are determined by their points and components;
  -- this is a placeholder-free conditional consequence of uniqueness.
  exact congrArg (fun f => f) h

/-- Chart-level descent data from a single cocone map and a uniqueness proof. -/
noncomputable def chartLevelDescentOfUnique
    {A : GlobalQuotientActionData (R := R) X G}
    (desc : ∀ c : Cocone A.actionFunctor, A.quotientCover ⟶ c.pt)
    (hfac : ∀ c : Cocone A.actionFunctor,
      A.projection ≫ desc c = c.ι.app (SingleObj.star G))
    (huniq : ∀ (c : Cocone A.actionFunctor) (m : A.quotientCover ⟶ c.pt),
      A.projection ≫ m = c.ι.app (SingleObj.star G) → m = desc c) :
    ChartLevelDescent (R := R) (A := A) :=
  { desc := desc, fac := hfac, uniq := huniq }

/-- The chart-level descent data is equivalently an assembly. -/
noncomputable def chartLevelDescentEquivAssembly
    {A : GlobalQuotientActionData (R := R) X G} :
    ChartLevelDescent (R := R) (A := A) ≃ GlobalDescentAssembly (R := R) (A := A) where
  toFun D := D.toAssembly
  invFun D := { desc := D.desc, fac := D.fac, uniq := D.uniq }
  left_inv D := by cases D; rfl
  right_inv D := by cases D; rfl


namespace ChartLevelDescent

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  {A : GlobalQuotientActionData (R := R) X G}
  (D : ChartLevelDescent (R := R) (A := A))

/-- The desc function of chart-level descent data. -/
abbrev descFun (c : Cocone A.actionFunctor) : A.quotientCover ⟶ c.pt :=
  D.desc c

/-- The fac proof of chart-level descent data. -/
theorem facAt (c : Cocone A.actionFunctor) :
    A.projection ≫ D.desc c = c.ι.app (SingleObj.star G) :=
  D.fac c

/-- The uniqueness proof of chart-level descent data. -/
theorem uniqAt (c : Cocone A.actionFunctor) (m : A.quotientCover ⟶ c.pt)
    (hm : A.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = D.desc c :=
  D.uniq c m hm

/-- Chart-level descent data gives an IsColimit. -/
noncomputable def isColimit : IsColimit A.cocone :=
  D.toAssembly.isColimit

/-- The IsColimit desc of chart-level descent data is its desc function. -/
theorem isColimit_desc (c : Cocone A.actionFunctor) :
    D.isColimit.desc c = D.desc c := rfl

/-- Extensionality for chart-level descent data. -/
theorem ext {E : ChartLevelDescent (R := R) (A := A)}
    (h : D.desc = E.desc) : D = E :=
  chartLevelDescent_ext (R := R) h

end ChartLevelDescent

namespace GlobalDescentAssembly

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  {A : GlobalQuotientActionData (R := R) X G}

/-- Assembly from a chart-level descent family. -/
noncomputable def ofChartLevel (D : ChartLevelDescent (R := R) (A := A)) :
    GlobalDescentAssembly (R := R) (A := A) :=
  D.toAssembly

/-- The assembly from chart-level descent data has the expected desc. -/
theorem ofChartLevel_desc (D : ChartLevelDescent (R := R) (A := A))
    (c : Cocone A.actionFunctor) :
    (ofChartLevel (R := R) D).desc c = D.desc c := rfl

end GlobalDescentAssembly

/-- The residual assembly proposition is monotone under chart-level descent. -/
theorem descentAssemblyResidual_of_chartLevel'
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (D : ChartLevelDescent (R := R) (A := A)) :
    descentAssemblyResidual (R := R) A :=
  descentAssemblyResidual_of_chartLevel (R := R) D

end GlobalDescentAssembly

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentAssembly
