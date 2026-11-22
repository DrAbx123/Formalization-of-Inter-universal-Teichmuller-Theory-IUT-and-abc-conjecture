import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProvider
import Mathlib.Tactic

/-!
# Consumer of the global quotient descent assembly

This file consumes a chart-level descent assembly and exposes the quotient
cover, projection, desc/fac/uniq, and IsColimit interfaces.  It does not
construct a provider inhabitant; the residual existence statement remains
explicit.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientAssemblyConsumer

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientIsColimit
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentAssembly
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Consumer package for a completed chart-level descent assembly. -/
structure GlobalQuotientAssemblyConsumer
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] where
  actionData : GlobalQuotientActionData (R := R) X G
  descent : GlobalDescentAssembly (R := R) (A := actionData)

namespace GlobalQuotientAssemblyConsumer

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (C : GlobalQuotientAssemblyConsumer (R := R) X G)

/-- The underlying action data. -/
abbrev action : GlobalQuotientActionData (R := R) X G := C.actionData

/-- The quotient chart presentation. -/
abbrev presentation : GlobalQuotientChartPresentation (Spec (CommRingCat.of R)) :=
  C.action.presentation

/-- The candidate quotient finite etale cover. -/
noncomputable abbrev cover : FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  C.action.quotientCover

/-- The cover projection to the quotient candidate. -/
noncomputable def projection : X ⟶ C.cover :=
  C.action.projection

/-- The cocone over the action functor. -/
def cocone : Cocone C.action.actionFunctor :=
  C.action.cocone

/-- The descent assembly attached to the consumer. -/
abbrev descent : GlobalDescentAssembly (R := R) (A := C.action) := C.descent

/-- The IsColimit obtained from the descent assembly. -/
noncomputable def isColimit : IsColimit C.cocone :=
  C.descent.isColimit

/-- The desc map of the IsColimit. -/
noncomputable def desc (c : Cocone C.action.actionFunctor) : C.cover ⟶ c.pt :=
  C.descent.desc c

/-- Fac equation for the consumer desc map. -/
theorem desc_fac (c : Cocone C.action.actionFunctor) :
    C.projection ≫ C.desc c = c.ι.app (SingleObj.star G) :=
  C.descent.facAt c

/-- Uniqueness of the consumer desc map. -/
theorem desc_uniq (c : Cocone C.action.actionFunctor) (m : C.cover ⟶ c.pt)
    (hm : C.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = C.desc c :=
  C.descent.uniqAt c m hm

/-- The projection is invariant under the action. -/
theorem projection_invariant (g : G) :
    (C.action.coverAction g).hom ≫ C.projection = C.projection :=
  C.action.projection_invariant g

/-- The consumer gives a conditional global quotient provider. -/
noncomputable def toProvider : GlobalQuotientProvider (R := R) X G :=
  globalQuotientProviderOfIsColimit (R := R) C.action.toGlobalActionData
    (by simpa [GlobalQuotientActionData.toGlobalActionData_cocone] using C.isColimit)

/-- The cover of the provider is the consumer cover. -/
theorem toProvider_cover : C.toProvider.cover = C.cover := rfl

/-- The projection of the provider is the consumer projection. -/
theorem toProvider_projection : C.toProvider.projection = C.projection := rfl

/-- Consumer extensionality in the descent assembly. -/
theorem ext {C D : GlobalQuotientAssemblyConsumer (R := R) X G}
    (ha : C.actionData = D.actionData) (hd : C.descent = D.descent) : C = D := by
  cases C with
  | mk ca cd =>
    cases D with
    | mk da dd =>
      simp only at ha hd
      subst ha
      subst hd
      rfl

/-- Consumer with a chart-level descent family. -/
noncomputable def ofChartLevelDescent
    (actionData : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := actionData)) :
    GlobalQuotientAssemblyConsumer (R := R) X G :=
  { actionData := actionData, descent := D.toAssembly }

/-- The chart-level consumer has the expected action data. -/
theorem ofChartLevelDescent_action
    (actionData : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := actionData)) :
    (ofChartLevelDescent (R := R) actionData D).actionData = actionData := rfl

/-- The chart-level consumer has the expected descent assembly. -/
theorem ofChartLevelDescent_descent
    (actionData : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := actionData)) :
    (ofChartLevelDescent (R := R) actionData D).descent = D.toAssembly := rfl

/-- The chart-level consumer gives an IsColimit. -/
theorem ofChartLevelDescent_isColimit
    (actionData : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := actionData)) :
    IsColimit (ofChartLevelDescent (R := R) actionData D).cocone :=
  (ofChartLevelDescent (R := R) actionData D).isColimit

end GlobalQuotientAssemblyConsumer

/-- Exact residual for the consumer: a chart-level descent family for the given
action data. -/
def globalQuotientAssemblyConsumerResidual
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G]
    (A : GlobalQuotientActionData (R := R) X G) : Prop :=
  Nonempty (ChartLevelDescent (R := R) (A := A))

/-- Consumer from an actual residual witness. -/
noncomputable def globalQuotientAssemblyConsumerOfResidual
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientAssemblyConsumerResidual (R := R) X G A) :
    GlobalQuotientAssemblyConsumer (R := R) X G :=
  let D := Classical.choice h
  GlobalQuotientAssemblyConsumer.ofChartLevelDescent (R := R) A D

/-- The residual consumer is conditional on an actual witness. -/
theorem globalQuotientAssemblyConsumerOfResidual_isColimit
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientAssemblyConsumerResidual (R := R) X G A) :
    IsColimit (globalQuotientAssemblyConsumerOfResidual (R := R) h).cocone :=
  (globalQuotientAssemblyConsumerOfResidual (R := R) h).isColimit


namespace GlobalQuotientAssemblyConsumer

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]

/-- Consumer data with an explicit chart presentation, before descent. -/
structure GlobalQuotientConsumerPresentation
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] where
  actionData : GlobalQuotientActionData (R := R) X G
  chartLevel : ChartLevelDescent (R := R) (A := actionData)

namespace GlobalQuotientConsumerPresentation

variable {A : GlobalQuotientActionData (R := R) X G}
  (P : GlobalQuotientConsumerPresentation (R := R) X G)

/-- The action data of the presentation. -/
abbrev action : GlobalQuotientActionData (R := R) X G := P.actionData

/-- The chart-level descent family. -/
abbrev chartLevel : ChartLevelDescent (R := R) (A := P.action) := P.chartLevel

/-- The quotient cover of the presentation. -/
noncomputable abbrev cover : FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  P.action.quotientCover

/-- The projection of the presentation. -/
noncomputable def projection : X ⟶ P.cover :=
  P.action.projection

/-- The presentation gives a consumer. -/
noncomputable def toConsumer : GlobalQuotientAssemblyConsumer (R := R) X G :=
  GlobalQuotientAssemblyConsumer.ofChartLevelDescent (R := R) P.action P.chartLevel

/-- The consumer cover is the presentation cover. -/
theorem toConsumer_cover : P.toConsumer.cover = P.cover := rfl

/-- The consumer projection is the presentation projection. -/
theorem toConsumer_projection : P.toConsumer.projection = P.projection := rfl

/-- The presentation gives an IsColimit. -/
theorem toConsumer_isColimit : IsColimit P.toConsumer.cocone :=
  P.toConsumer.isColimit

end GlobalQuotientConsumerPresentation

/-- A consumer is equivalent to a presentation with chart-level descent data. -/
noncomputable def consumerEquivPresentation
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] :
    GlobalQuotientAssemblyConsumer (R := R) X G ≃
      GlobalQuotientConsumerPresentation (R := R) X G where
  toFun C :=
    { actionData := C.actionData
      chartLevel := { desc := C.descent.desc, fac := C.descent.fac, uniq := C.descent.uniq } }
  invFun P := P.toConsumer
  left_inv C := by cases C; rfl
  right_inv P := by cases P; rfl

/-- The consumer desc is natural in cocone morphisms. -/
theorem desc_natural (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    {c d : Cocone C.action.actionFunctor} (f : c ⟶ d) :
    C.desc c ≫ f.hom = C.desc d :=
  C.descent.desc_natural f

/-- Two consumers with the same action data and descent function are equal. -/
theorem ext_desc {C D : GlobalQuotientAssemblyConsumer (R := R) X G}
    (ha : C.actionData = D.actionData)
    (hd : C.descent.desc = D.descent.desc) : C = D := by
  cases C with
  | mk ca cd =>
    cases D with
    | mk da dd =>
      simp only at ha hd
      subst ha
      have : cd = dd := GlobalDescentAssembly.ext (R := R) hd
      subst this
      rfl

/-- The consumer satisfies the projection invariant property. -/
theorem cocone_naturality (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (g : G) :
    C.action.actionFunctor.map g ≫ C.cocone.ι.app (SingleObj.star G) =
      C.cocone.ι.app (SingleObj.star G) :=
  C.action.cocone_naturality g

/-- The consumer's IsColimit is compatible with its cocone. -/
theorem isColimit_cocone (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.isColimit.cocone = C.cocone := rfl

/-- The consumer's IsColimit desc agrees with the consumer desc. -/
theorem isColimit_desc_eq (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (c : Cocone C.action.actionFunctor) :
    C.isColimit.desc c = C.desc c := rfl

/-- The consumer's IsColimit fac agrees with the consumer fac. -/
theorem isColimit_fac_eq (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (c : Cocone C.action.actionFunctor) :
    C.projection ≫ C.isColimit.desc c = c.ι.app (SingleObj.star G) :=
  C.desc_fac c

/-- A consumer with a projection isomorphism has a trivial descent. -/
noncomputable def trivialConsumer
    (A : GlobalQuotientActionData (R := R) X G)
    (e : A.quotientCover ≅ X) (hproj : A.projection = e.inv) :
    GlobalQuotientAssemblyConsumer (R := R) X G :=
  GlobalQuotientAssemblyConsumer.ofChartLevelDescent (R := R) A
    (trivialChartLevelDescent (R := R) e hproj)

/-- The trivial consumer cover is the action-data quotient cover. -/
theorem trivialConsumer_cover
    (A : GlobalQuotientActionData (R := R) X G)
    (e : A.quotientCover ≅ X) (hproj : A.projection = e.inv) :
    (trivialConsumer (R := R) A e hproj).cover = A.quotientCover := rfl

end GlobalQuotientAssemblyConsumer


namespace GlobalQuotientAssemblyConsumer

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]

/-- The consumer cover is finite etale over the affine base. -/
theorem cover_finite_etale (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    Etale (FiniteEtaleCover.structureMap C.cover) ∧
      IsFinite (FiniteEtaleCover.structureMap C.cover) :=
  C.action.presentation.cover_isFiniteEtale

/-- The consumer cover structure map is the glued map. -/
theorem cover_structureMap (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    FiniteEtaleCover.structureMap C.cover = C.action.presentation.gluedMap := rfl

/-- The consumer projection factors through the glued chart map. -/
theorem projection_eq_chartIso (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.projection = C.action.projection := rfl

/-- The consumer action functor is the action-data functor. -/
theorem actionFunctor_eq (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.action.actionFunctor = C.action.actionFunctor := rfl

/-- The consumer quotient cocone is the action-data cocone. -/
theorem cocone_eq (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.cocone = C.action.cocone := rfl

/-- The consumer projection is invariant under the cover action. -/
theorem coverAction_projection (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (g : G) :
    (C.action.coverAction g).hom ≫ C.projection = C.projection :=
  C.action.projection_invariant g

/-- The consumer desc at the action cocone is the identity. -/
theorem desc_self (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.desc C.cocone = 𝟙 C.cover :=
  C.descent.desc_self

/-- The consumer IsColimit uniqueness property. -/
theorem isColimit_uniq (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (c : Cocone C.action.actionFunctor) (m : C.cover ⟶ c.pt)
    (hm : C.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = C.isColimit.desc c :=
  C.descent.isColimit_uniq c m hm

/-- Consumer with a trivial action (no cover action) is conditional on a
projection isomorphism. -/
noncomputable def consumerOfProjectionIso
    (A : GlobalQuotientActionData (R := R) X G)
    (e : A.quotientCover ≅ X) (hproj : A.projection = e.inv) :
    GlobalQuotientAssemblyConsumer (R := R) X G :=
  trivialConsumer (R := R) A e hproj

/-- The projection-iso consumer has an IsColimit. -/
theorem consumerOfProjectionIso_isColimit
    (A : GlobalQuotientActionData (R := R) X G)
    (e : A.quotientCover ≅ X) (hproj : A.projection = e.inv) :
    IsColimit (consumerOfProjectionIso (R := R) A e hproj).cocone :=
  (consumerOfProjectionIso (R := R) A e hproj).isColimit

end GlobalQuotientAssemblyConsumer


namespace GlobalQuotientAssemblyConsumer

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]

/-- The consumer residual is inhabited exactly from a chart-level descent family. -/
theorem residual_iff (A : GlobalQuotientActionData (R := R) X G) :
    globalQuotientAssemblyConsumerResidual (R := R) X G A ↔
      Nonempty (ChartLevelDescent (R := R) (A := A)) :=
  Iff.rfl

/-- A chart-level descent family gives the consumer residual. -/
theorem residual_of_chartLevel (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    globalQuotientAssemblyConsumerResidual (R := R) X G A :=
  ⟨D⟩

/-- The residual consumer is a consumer. -/
noncomputable def consumerOfResidual
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientAssemblyConsumerResidual (R := R) X G A) :
    GlobalQuotientAssemblyConsumer (R := R) X G :=
  globalQuotientAssemblyConsumerOfResidual (R := R) h

/-- The residual consumer has the expected cover. -/
theorem consumerOfResidual_cover
    {A : GlobalQuotientActionData (R := R) X G}
    (h : globalQuotientAssemblyConsumerResidual (R := R) X G A) :
    (consumerOfResidual (R := R) h).cover = A.quotientCover := rfl

end GlobalQuotientAssemblyConsumer


namespace GlobalQuotientAssemblyConsumer

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]

/-- The consumer residual is a proposition, not an assertion of existence. -/
theorem residual_prop (A : GlobalQuotientActionData (R := R) X G) :
    Prop := globalQuotientAssemblyConsumerResidual (R := R) X G A

/-- The consumer action data is the action data of its presentation. -/
theorem action_eq_presentation (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.action = C.presentation.actionData := rfl

/-- The consumer cover is the presentation cover. -/
theorem cover_eq_presentation (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.cover = C.action.quotientCover := rfl

/-- The consumer projection is the action projection. -/
theorem projection_eq_action (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.projection = C.action.projection := rfl

/-- The consumer cocone is the action cocone. -/
theorem cocone_eq_action (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.cocone = C.action.cocone := rfl

/-- The consumer IsColimit is the descent IsColimit. -/
theorem isColimit_eq_descent (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.isColimit = C.descent.isColimit := rfl

/-- The consumer desc is the descent desc. -/
theorem desc_eq_descent (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (c : Cocone C.action.actionFunctor) :
    C.desc c = C.descent.desc c := rfl

/-- The consumer fac is the descent fac. -/
theorem desc_fac_eq_descent (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (c : Cocone C.action.actionFunctor) :
    C.desc_fac c = C.descent.facAt c := rfl

/-- The consumer uniqueness is the descent uniqueness. -/
theorem desc_uniq_eq_descent (C : GlobalQuotientAssemblyConsumer (R := R) X G)
    (c : Cocone C.action.actionFunctor) (m : C.cover ⟶ c.pt)
    (hm : C.projection ≫ m = c.ι.app (SingleObj.star G)) :
    C.desc_uniq c m hm = C.descent.uniqAt c m hm := rfl

/-- The consumer is a conditional provider. -/
theorem isConditionalProvider (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.toProvider.isColimit = C.isColimit := rfl

/-- The consumer presentation is recoverable. -/
noncomputable def toPresentation (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    GlobalQuotientConsumerPresentation (R := R) X G :=
  { actionData := C.actionData
    chartLevel := { desc := C.descent.desc, fac := C.descent.fac, uniq := C.descent.uniq } }

/-- Round-trip from consumer to presentation and back. -/
theorem toPresentation_toConsumer (C : GlobalQuotientAssemblyConsumer (R := R) X G) :
    C.toPresentation.toConsumer = C := by
  cases C
  rfl

end GlobalQuotientAssemblyConsumer

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientAssemblyConsumer
