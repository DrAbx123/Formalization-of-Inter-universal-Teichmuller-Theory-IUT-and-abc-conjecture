import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientAssemblyConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentFinal
import Mathlib.Tactic

/-!
# Consumer assembly from chart-level descent

This file consumes an actual chart-level descent family and assembles the
global quotient cover, projection, desc/fac/uniq, and IsColimit.  It does not
assert an unconditional provider inhabitant; the residual existence condition
is recorded as a proposition.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientConsumerAssembly

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentAssembly
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientAssemblyConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentFinal
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Actual chart-level descent input for the consumer assembly. -/
structure ConsumerAssemblyInput
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] where
  actionData : GlobalQuotientActionData (R := R) X G
  chartLevel : ChartLevelDescent (R := R) (A := actionData)

namespace ConsumerAssemblyInput

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (I : ConsumerAssemblyInput (R := R) X G)

/-- The action data. -/
abbrev action : GlobalQuotientActionData (R := R) X G := I.actionData

/-- The chart-level descent family. -/
abbrev chartLevel : ChartLevelDescent (R := R) (A := I.action) := I.chartLevel

/-- The assembled global quotient cover. -/
noncomputable abbrev cover : FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  I.action.quotientCover

/-- The projection from X to the assembled quotient. -/
noncomputable def projection : X ⟶ I.cover :=
  I.action.projection

/-- The action cocone. -/
def cocone : Cocone I.action.actionFunctor :=
  I.action.cocone

/-- The descent assembly. -/
noncomputable def assembly : GlobalDescentAssembly (R := R) (A := I.action) :=
  I.chartLevel.toAssembly

/-- The consumer assembly. -/
noncomputable def consumer : GlobalQuotientAssemblyConsumer (R := R) X G :=
  GlobalQuotientAssemblyConsumer.ofChartLevelDescent (R := R) I.action I.chartLevel

/-- The final assembly package. -/
noncomputable def final : GlobalQuotientDescentFinal (R := R) X G :=
  GlobalQuotientDescentFinal.ofChartLevel (R := R) I.action I.chartLevel

/-- The assembled IsColimit. -/
noncomputable def isColimit : IsColimit I.cocone :=
  I.assembly.isColimit

/-- The assembled desc map. -/
noncomputable def desc (c : Cocone I.action.actionFunctor) : I.cover ⟶ c.pt :=
  I.chartLevel.desc c

/-- The assembled fac equation. -/
theorem desc_fac (c : Cocone I.action.actionFunctor) :
    I.projection ≫ I.desc c = c.ι.app (SingleObj.star G) :=
  I.chartLevel.facAt c

/-- The assembled uniqueness property. -/
theorem desc_uniq (c : Cocone I.action.actionFunctor) (m : I.cover ⟶ c.pt)
    (hm : I.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = I.desc c :=
  I.chartLevel.uniqAt c m hm

/-- The assembled cover is the action quotient cover. -/
theorem cover_eq : I.cover = I.action.quotientCover := rfl

/-- The assembled projection is the action projection. -/
theorem projection_eq : I.projection = I.action.projection := rfl

/-- The assembled consumer cover equals the input cover. -/
theorem consumer_cover : I.consumer.cover = I.cover := rfl

/-- The assembled final cover equals the input cover. -/
theorem final_cover : I.final.cover = I.cover := rfl

/-- The assembled consumer IsColimit equals the assembled IsColimit. -/
theorem consumer_isColimit : I.consumer.isColimit = I.isColimit := rfl

/-- The assembled final IsColimit equals the assembled IsColimit. -/
theorem final_isColimit : I.final.isColimit = I.isColimit := rfl

/-- The input gives a conditional provider. -/
noncomputable def provider : GlobalQuotientProvider (R := R) X G :=
  I.consumer.toProvider

/-- The provider cover is the assembled cover. -/
theorem provider_cover : I.provider.cover = I.cover := rfl

/-- The provider projection is the assembled projection. -/
theorem provider_projection : I.provider.projection = I.projection := rfl

/-- The chart-level descent witness is explicitly retained. -/
theorem chartLevel_witness : Nonempty (ChartLevelDescent (R := R) (A := I.action)) :=
  ⟨I.chartLevel⟩

end ConsumerAssemblyInput

/-- Consumer assembly from an actual chart-level descent witness. -/
noncomputable def consumerAssembly
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    ConsumerAssemblyInput (R := R) X G :=
  { actionData := A, chartLevel := D }

/-- The consumer assembly has the action data as input. -/
theorem consumerAssembly_action
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    (consumerAssembly (R := R) A D).action = A := rfl

/-- The consumer assembly has the chart-level descent as input. -/
theorem consumerAssembly_chartLevel
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    (consumerAssembly (R := R) A D).chartLevel = D := rfl

/-- The consumer assembly gives an IsColimit. -/
theorem consumerAssembly_isColimit
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (A : GlobalQuotientActionData (R := R) X G)
    (D : ChartLevelDescent (R := R) (A := A)) :
    IsColimit (consumerAssembly (R := R) A D).cocone :=
  (consumerAssembly (R := R) A D).isColimit

/-- Exact residual: existence of a chart-level descent family for the action
data.  This is a proposition, not an asserted inhabitant. -/
def consumerAssemblyResidual
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G]
    (A : GlobalQuotientActionData (R := R) X G) : Prop :=
  Nonempty (ChartLevelDescent (R := R) (A := A))

/-- Consumer assembly from a residual witness. -/
noncomputable def consumerAssemblyOfResidual
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (h : consumerAssemblyResidual (R := R) X G A) :
    ConsumerAssemblyInput (R := R) X G :=
  let D := Classical.choice h
  consumerAssembly (R := R) A D

/-- The residual consumer assembly gives an IsColimit. -/
theorem consumerAssemblyOfResidual_isColimit
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (h : consumerAssemblyResidual (R := R) X G A) :
    IsColimit (consumerAssemblyOfResidual (R := R) h).cocone :=
  (consumerAssemblyOfResidual (R := R) h).isColimit


namespace ConsumerAssemblyInput

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (I : ConsumerAssemblyInput (R := R) X G)

/-- The assembled consumer has the same projection as the input. -/
theorem consumer_projection :
    I.consumer.projection = I.projection := rfl

/-- The assembled final has the same projection as the input. -/
theorem final_projection :
    I.final.projection = I.projection := rfl

/-- The assembled consumer action data is the input action data. -/
theorem consumer_actionData :
    I.consumer.actionData = I.actionData := rfl

/-- The assembled final action data is the input action data. -/
theorem final_actionData :
    I.final.actionData = I.actionData := rfl

/-- The assembled consumer descent desc is the chart-level desc. -/
theorem consumer_desc (c : Cocone I.action.actionFunctor) :
    I.consumer.desc c = I.chartLevel.desc c := rfl

/-- The assembled final desc is the chart-level desc. -/
theorem final_desc (c : Cocone I.action.actionFunctor) :
    I.final.chartLevel.desc c = I.chartLevel.desc c := rfl

/-- The assembled consumer fac is the chart-level fac. -/
theorem consumer_desc_fac (c : Cocone I.action.actionFunctor) :
    I.consumer.projection ≫ I.consumer.desc c =
      c.ι.app (SingleObj.star G) :=
  I.consumer.desc_fac c

/-- The assembled final fac is the chart-level fac. -/
theorem final_desc_fac (c : Cocone I.action.actionFunctor) :
    I.final.projection ≫ I.final.chartLevel.desc c =
      c.ι.app (SingleObj.star G) :=
  I.final.desc_fac c

/-- The assembled consumer uniqueness is the chart-level uniqueness. -/
theorem consumer_desc_uniq (c : Cocone I.action.actionFunctor)
    (m : I.consumer.cover ⟶ c.pt)
    (hm : I.consumer.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = I.consumer.desc c :=
  I.consumer.desc_uniq c m hm

/-- The assembled final uniqueness is the chart-level uniqueness. -/
theorem final_desc_uniq (c : Cocone I.action.actionFunctor)
    (m : I.final.cover ⟶ c.pt)
    (hm : I.final.projection ≫ m = c.ι.app (SingleObj.star G)) :
    m = I.final.chartLevel.desc c :=
  I.final.desc_uniq c m hm

/-- The assembled consumer is a conditional provider. -/
theorem consumer_isConditionalProvider :
    I.consumer.toProvider.isColimit = I.isColimit := rfl

/-- The input can be extended by a final package. -/
noncomputable def extendFinal : GlobalQuotientDescentFinal (R := R) X G := I.final

/-- The extended final cover is the assembled cover. -/
theorem extendFinal_cover : I.extendFinal.cover = I.cover := rfl

end ConsumerAssemblyInput

/-- The consumer assembly residual is the chart-level descent existence. -/
theorem consumerAssemblyResidual_iff
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G]
    (A : GlobalQuotientActionData (R := R) X G) :
    consumerAssemblyResidual (R := R) X G A ↔
      Nonempty (ChartLevelDescent (R := R) (A := A)) :=
  Iff.rfl

/-- A chart-level descent witness gives the residual. -/
theorem consumerAssemblyResidual_of_chartLevel
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (D : ChartLevelDescent (R := R) (A := A)) :
    consumerAssemblyResidual (R := R) X G A :=
  ⟨D⟩


namespace ConsumerAssemblyInput

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (I : ConsumerAssemblyInput (R := R) X G)

/-- The consumer assembly projection is invariant. -/
theorem projection_invariant (g : G) :
    (I.action.coverAction g).hom ≫ I.projection = I.projection :=
  I.action.projection_invariant g

/-- The consumer assembly action functor is the action data functor. -/
theorem actionFunctor_eq : I.action.actionFunctor = I.action.actionFunctor := rfl

/-- The consumer assembly cocone is the action cocone. -/
theorem cocone_eq : I.cocone = I.action.cocone := rfl

/-- The consumer assembly assembly is the chart-level assembly. -/
theorem assembly_eq : I.assembly = I.chartLevel.toAssembly := rfl

/-- The consumer assembly final provider is the consumer provider. -/
theorem provider_eq : I.provider = I.consumer.toProvider := rfl

/-- The consumer assembly final package has the same final cover. -/
theorem final_cover_eq : I.final.cover = I.cover := rfl

/-- The consumer assembly final package has the same final projection. -/
theorem final_projection_eq : I.final.projection = I.projection := rfl

/-- The consumer assembly final package has the same final IsColimit. -/
theorem final_isColimit_eq : I.final.isColimit = I.isColimit := rfl

/-- The consumer assembly final package has the same consumer. -/
theorem final_consumer_eq : I.final.consumer = I.consumer := rfl

/-- A consumer assembly restricted to the same action data but with a supplied
chart-level descent family. -/
noncomputable def withChartLevel
    (D : ChartLevelDescent (R := R) (A := I.action)) :
    ConsumerAssemblyInput (R := R) X G :=
  { actionData := I.action, chartLevel := D }

/-- Restriction preserves the action data. -/
theorem withChartLevel_action
    (D : ChartLevelDescent (R := R) (A := I.action)) :
    (I.withChartLevel (R := R) D).action = I.action := rfl

/-- Restriction changes the chart-level descent data. -/
theorem withChartLevel_chartLevel
    (D : ChartLevelDescent (R := R) (A := I.action)) :
    (I.withChartLevel (R := R) D).chartLevel = D := rfl

end ConsumerAssemblyInput

/-- A named witness for the consumer assembly residual. -/
structure ConsumerAssemblyResidualWitness
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G]
    (A : GlobalQuotientActionData (R := R) X G) where
  chartLevel : ChartLevelDescent (R := R) (A := A)

namespace ConsumerAssemblyResidualWitness

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  {A : GlobalQuotientActionData (R := R) X G}
  (W : ConsumerAssemblyResidualWitness (R := R) X G A)

/-- The witness gives the consumer assembly input. -/
noncomputable def toInput : ConsumerAssemblyInput (R := R) X G :=
  consumerAssembly (R := R) A W.chartLevel

/-- The witness input has an IsColimit. -/
theorem toInput_isColimit : IsColimit W.toInput.cocone :=
  W.toInput.isColimit

/-- The witness is the same as the residual proposition. -/
theorem nonempty_residual : consumerAssemblyResidual (R := R) X G A :=
  ⟨W.chartLevel⟩

/-- The witness gives a conditional global quotient provider. -/
noncomputable def provider : GlobalQuotientProvider (R := R) X G :=
  W.toInput.provider

end ConsumerAssemblyResidualWitness

/-- The residual proposition is equivalent to the witness type. -/
theorem consumerAssemblyResidual_iff_witness
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G]
    (A : GlobalQuotientActionData (R := R) X G) :
    consumerAssemblyResidual (R := R) X G A ↔
      Nonempty (ConsumerAssemblyResidualWitness (R := R) X G A) :=
  Iff.rfl

/-- Build a witness from chart-level descent data. -/
def ConsumerAssemblyResidualWitness.ofChartLevel
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (D : ChartLevelDescent (R := R) (A := A)) :
    ConsumerAssemblyResidualWitness (R := R) X G A :=
  { chartLevel := D }

/-- The consumer assembly from a witness. -/
noncomputable def consumerAssemblyOfWitness
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (W : ConsumerAssemblyResidualWitness (R := R) X G A) :
    ConsumerAssemblyInput (R := R) X G :=
  W.toInput

/-- The witness consumer assembly has an IsColimit. -/
theorem consumerAssemblyOfWitness_isColimit
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    {A : GlobalQuotientActionData (R := R) X G}
    (W : ConsumerAssemblyResidualWitness (R := R) X G A) :
    IsColimit (consumerAssemblyOfWitness (R := R) W).cocone :=
  W.toInput_isColimit

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientConsumerAssembly

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientConsumerAssembly

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientConsumerAssembly
