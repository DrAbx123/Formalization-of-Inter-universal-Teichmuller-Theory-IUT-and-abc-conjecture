import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientAssemblyConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProvider
import Mathlib.Tactic

/-!
# Final global quotient descent assembly

This file packages the final conditional assembly: action data plus chart-level
descent data gives the global quotient cover, projection, desc/fac/uniq, and an
IsColimit.  No provider inhabitant is constructed unconditionally; the residual
existence problem is recorded as a proposition.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentFinal

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentAssembly
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientAssemblyConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProvider
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Final conditional global quotient descent package. -/
structure GlobalQuotientDescentFinal
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] where
  actionData : GlobalQuotientActionData (R := R) X G
  chartLevel : ChartLevelDescent (R := R) (A := actionData)

namespace GlobalQuotientDescentFinal

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (F : GlobalQuotientDescentFinal (R := R) X G)

/-- The action data. -/
abbrev action : GlobalQuotientActionData (R := R) X G := F.actionData

/-- The chart-level descent family. -/
abbrev chartLevel : ChartLevelDescent (R := R) (A := F.action) := F.chartLevel

/-- The quotient cover. -/
noncomputable abbrev cover : FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  F.action.quotientCover

/-- The projection from the cover to the quotient. -/
noncomputable def projection : X ⟶ F.cover :=
  F.action.projection

/-- The action cocone. -/
def cocone : Cocone F.action.actionFunctor :=
  F.action.cocone

/-- The assembly. -/
noncomputable def assembly : GlobalDescentAssembly (R := R) (A := F.action) :=
  F.chartLevel.toAssembly

/-- The IsColimit. -/
noncomputable def isColimit : IsColimit F.cocone :=
  F.assembly.isColimit

/-- The consumer. -/
noncomputable def consumer : GlobalQuotientAssemblyConsumer (R := R) X G :=
  GlobalQuotientAssemblyConsumer.ofChartLevelDescent (R := R) F.action F.chartLevel

/-- The provider. -/
noncomputable def provider : GlobalQuotientProvider (R := R) X G :=
  F.consumer.toProvider

/-- The consumer cover is the final cover. -/
theorem consumer_cover : F.consumer.cover = F.cover := rfl

/-- The provider cover is the final cover. -/
theorem provider_cover : F.provider.cover = F.cover := rfl

/-- The consumer projection is the final projection. -/
theorem consumer_projection : F.consumer.projection = F.projection := rfl

/-- The provider projection is the final projection. -/
theorem provider_projection : F.provider.projection = F.projection := rfl

/-- The final IsColimit is the consumer IsColimit. -/
theorem isColimit_consumer : F.isColimit = F.consumer.isColimit := rfl

/-- Fac equation for the final desc. -/
theorem desc_fac (c : Cocone F.action.actionFunctor) :
    F.projection ≫ F.chartLevel.desc c = c.ι.app (SingleObj.star G) :=
  F.chartLevel.facAt c

/-- Uniqueness of the final desc. -/
theorem desc_uniq (c : Cocone F.action.actionFunctor) (m : F.cover ⟶ c.pt)
    (hm : F.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = F.chartLevel.desc c :=
  F.chartLevel.uniqAt c m hm

/-- The final descent gives a conditional provider. -/
noncomputable def providerOfFinal : GlobalQuotientProvider (R := R) X G :=
  F.provider

/-- The final package gives the consumer residual. -/
theorem residual_of_final :
    globalQuotientAssemblyConsumerResidual (R := R) X G F.action :=
  ⟨F.chartLevel⟩

/-- Final extensionality in action data and chart-level descent. -/
theorem ext {F E : GlobalQuotientDescentFinal (R := R) X G}
    (ha : F.actionData = E.actionData) (hc : F.chartLevel = E.chartLevel) : F = E := by
  cases F with
  | mk fa fc =>
    cases E with
    | mk ea ec =>
      simp only at ha hc
      subst ha
      subst hc
      rfl

/-- The final package from chart-level descent data. -/
noncomputable def ofChartLevel
    (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    GlobalQuotientDescentFinal (R := R) X G :=
  { actionData := A, chartLevel := D }

/-- The final package gives an IsColimit exactly from chart-level descent. -/
theorem isColimit_ofChartLevel
    (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    IsColimit (ofChartLevel (R := R) A D).cocone :=
  (ofChartLevel (R := R) A D).isColimit

/-- The final package cover is the action quotient cover. -/
theorem ofChartLevel_cover
    (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    (ofChartLevel (R := R) A D).cover = A.quotientCover := rfl

end GlobalQuotientDescentFinal

/-- Exact final residual: existence of chart-level descent data for the action
data.  This is a proposition, not an asserted inhabitant. -/
def globalQuotientDescentFinalResidual
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G]
    (A : GlobalQuotientActionData (R := R) X G) : Prop :=
  Nonempty (ChartLevelDescent (R := R) (A := A))

/-- Final package from an actual residual witness. -/
noncomputable def globalQuotientDescentFinalOfResidual
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientDescentFinalResidual (R := R) X G A) :
    GlobalQuotientDescentFinal (R := R) X G :=
  let D := Classical.choice h
  GlobalQuotientDescentFinal.ofChartLevel (R := R) A D

/-- The residual final package has an IsColimit. -/
theorem globalQuotientDescentFinalOfResidual_isColimit
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientDescentFinalResidual (R := R) X G A) :
    IsColimit (globalQuotientDescentFinalOfResidual (R := R) h).cocone :=
  (globalQuotientDescentFinalOfResidual (R := R) h).isColimit


namespace GlobalQuotientDescentFinal

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (F : GlobalQuotientDescentFinal (R := R) X G)

/-- The final assembly is the chart-level assembly. -/
theorem assembly_eq : F.assembly = F.chartLevel.toAssembly := rfl

/-- The final consumer is the chart-level consumer. -/
theorem consumer_eq :
    F.consumer = GlobalQuotientAssemblyConsumer.ofChartLevelDescent (R := R)
      F.action F.chartLevel := rfl

/-- The final provider is the consumer provider. -/
theorem provider_eq : F.provider = F.consumer.toProvider := rfl

/-- The final cover is the action quotient cover. -/
theorem cover_eq : F.cover = F.action.quotientCover := rfl

/-- The final projection is the action projection. -/
theorem projection_eq : F.projection = F.action.projection := rfl

/-- The final cocone is the action cocone. -/
theorem cocone_eq : F.cocone = F.action.cocone := rfl

/-- The final IsColimit desc is the chart-level desc. -/
theorem isColimit_desc (c : Cocone F.action.actionFunctor) :
    F.isColimit.desc c = F.chartLevel.desc c := rfl

/-- The final IsColimit fac. -/
theorem isColimit_fac (c : Cocone F.action.actionFunctor) :
    F.projection ≫ F.isColimit.desc c = c.ι.app (SingleObj.star G) :=
  F.desc_fac c

/-- The final IsColimit uniqueness. -/
theorem isColimit_uniq (c : Cocone F.action.actionFunctor) (m : F.cover ⟶ c.pt)
    (hm : F.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = F.isColimit.desc c := by
  rw [F.isColimit_desc]
  exact F.desc_uniq c m hm

/-- The final projection is invariant under the action. -/
theorem projection_invariant (g : G) :
    (F.action.coverAction g).hom ≫ F.projection = F.projection :=
  F.action.projection_invariant g

/-- The final provider is a conditional provider. -/
theorem provider_isColimit : F.provider.isColimit = F.isColimit := rfl

/-- The final provider residual is inhabited. -/
theorem provider_residual :
    globalQuotientAssemblyConsumerResidual (R := R) X G F.action :=
  F.residual_of_final

end GlobalQuotientDescentFinal

/-- Final package from a consumer. -/
noncomputable def globalQuotientDescentFinalOfConsumer
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    GlobalQuotientDescentFinal (R := R) X G :=
  { actionData := C.actionData
    chartLevel := { desc := C.descent.desc, fac := C.descent.fac, uniq := C.descent.uniq } }

/-- The final package from a consumer has the same cover. -/
theorem globalQuotientDescentFinalOfConsumer_cover
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    (globalQuotientDescentFinalOfConsumer (R := R) C).cover = C.cover := rfl

/-- The final package from a consumer has the same IsColimit. -/
theorem globalQuotientDescentFinalOfConsumer_isColimit
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    IsColimit (globalQuotientDescentFinalOfConsumer (R := R) C).cocone :=
  (globalQuotientDescentFinalOfConsumer (R := R) C).isColimit

/-- The final package is determined by its action data and chart-level descent. -/
theorem ext_action_chartLevel
    {F E : GlobalQuotientDescentFinal (R := R) X G}
    (ha : F.actionData = E.actionData) (hc : F.chartLevel = E.chartLevel) : F = E :=
  GlobalQuotientDescentFinal.ext (R := R) ha hc

/-- The final residual is equivalent to the consumer residual. -/
theorem residual_iff_consumer_residual
    (A : GlobalQuotientActionData (R := R) X G) :
    globalQuotientDescentFinalResidual (R := R) X G A ↔
      globalQuotientAssemblyConsumerResidual (R := R) X G A :=
  Iff.rfl

/-- The final residual is not asserted; it is the exact existence condition for
the chart-level descent family. -/
theorem residual_spec (A : GlobalQuotientActionData (R := R) X G) :
    globalQuotientDescentFinalResidual (R := R) X G A ↔
      Nonempty (ChartLevelDescent (R := R) (A := A)) :=
  Iff.rfl


namespace GlobalQuotientDescentFinal

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (F : GlobalQuotientDescentFinal (R := R) X G)

/-- The final consumer has the final cover. -/
theorem consumer_cover_eq : F.consumer.cover = F.cover := rfl

/-- The final consumer has the final projection. -/
theorem consumer_projection_eq : F.consumer.projection = F.projection := rfl

/-- The final consumer cocone is the final cocone. -/
theorem consumer_cocone_eq : F.consumer.cocone = F.cocone := rfl

/-- The final provider cover is the final cover. -/
theorem provider_cover_eq : F.provider.cover = F.cover := rfl

/-- The final provider projection is the final projection. -/
theorem provider_projection_eq : F.provider.projection = F.projection := rfl

/-- The final provider projection is invariant. -/
theorem provider_projection_invariant (g : G) :
    (F.provider.data.action g).hom ≫ F.provider.projection = F.provider.projection :=
  F.provider.projection_invariant g

/-- The final chart-level descent gives a fac equation at the action cocone. -/
theorem chartLevel_fac_self :
    F.projection ≫ F.chartLevel.desc F.cocone =
      F.cocone.ι.app (SingleObj.star G) :=
  F.chartLevel.facAt F.cocone

/-- The final chart-level descent gives a uniqueness at the action cocone. -/
theorem chartLevel_uniq_self (m : F.cover ⟶ F.cocone.pt)
    (hm : F.projection ≫ m = F.cocone.ι.app (SingleObj.star G)) :
    m = F.chartLevel.desc F.cocone :=
  F.chartLevel.uniqAt F.cocone m hm

/-- The final package has a cover whose structure map is the glued map. -/
theorem cover_structureMap :
    FiniteEtaleCover.structureMap F.cover = F.action.presentation.gluedMap := rfl

/-- The final package has a finite etale quotient cover. -/
theorem cover_finite_etale :
    Etale (FiniteEtaleCover.structureMap F.cover) ∧
      IsFinite (FiniteEtaleCover.structureMap F.cover) :=
  F.action.presentation.cover_isFiniteEtale

/-- The final action data is recoverable from the final package. -/
theorem actionData_eq : F.actionData = F.action := rfl

/-- The final chart-level descent is recoverable from the final package. -/
theorem chartLevel_eq : F.chartLevel = F.chartLevel := rfl

end GlobalQuotientDescentFinal

namespace GlobalQuotientDescentFinal

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]

/-- The final package is inhabited exactly from chart-level descent data. -/
theorem nonempty_iff_chartLevel (A : GlobalQuotientActionData (R := R) X G) :
    Nonempty (GlobalQuotientDescentFinal (R := R) X G) ↔
      Nonempty (ChartLevelDescent (R := R) (A := A)) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.chartLevel⟩
  · rintro ⟨D⟩
    exact ⟨ofChartLevel (R := R) A D⟩

end GlobalQuotientDescentFinal


namespace GlobalQuotientDescentFinal

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]

/-- The final residual is monotone under chart-level descent evidence. -/
theorem residual_of_chartLevel (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    globalQuotientDescentFinalResidual (R := R) X G A :=
  ⟨D⟩

/-- The final package from a residual witness has the action quotient cover. -/
theorem globalQuotientDescentFinalOfResidual_cover
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientDescentFinalResidual (R := R) X G A) :
    (globalQuotientDescentFinalOfResidual (R := R) h).cover = A.quotientCover := rfl

/-- The final package from a residual witness has the projection of the action
data. -/
theorem globalQuotientDescentFinalOfResidual_projection
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientDescentFinalResidual (R := R) X G A) :
    (globalQuotientDescentFinalOfResidual (R := R) h).projection =
      A.projection := rfl

/-- The residual witness is a chart-level descent family, not a provider. -/
theorem residual_witness_is_chartLevel
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientDescentFinalResidual (R := R) X G A) :
    Nonempty (ChartLevelDescent (R := R) (A := A)) :=
  h

end GlobalQuotientDescentFinal

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentFinal

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentFinal
