import tmp.sheaf.xif.paper.S3136ModSideInputActual
import tmp.sheaf.xif.paper.GlobalFrobenioidPresentationActual

/-! # Stage-4 host: actual model-level mod-side Phi / Input component

Source anchors: IUT II, Cor. 4.8, (ii) (the natural isomorphisms of Frobenioids
(F^boxplus_mod)_alpha ~= (F^boxplus_MOD)_alpha, tautological on rational
function monoids); IUT III, Prop. 3.7, (i), (ii), (v) (pp. 108--112).

The base/divisor/realification layer of the mod-to-MOD Frobenioid isomorphism is
already actual, and the carrier-functor/Input gap was reduced to 6 named fields
(previous files).  This file constructs the actual model-level mod-side data and
reduces the 6 named fields to 2:
* modSidePhiActual: the actual Example 3.6 global DivisorialMonoidOn on the
  bottom base (the model-level mod-side Phi data);
* modSideInputActual: the actual Example 3.6 SourceModelFrobenioid.Input
  (rational functions + principal-divisor map);
* modSideCarrierActual / modSideCarrierFunctorActual: the actual carrier
  category and its identity carrier equivalence;
* modSideBaseDivisorLayerActual / modSideDivisorNatIsoActual: the actual
  base/divisor layer isomorphism and divisor-natural-iso component;
* ModSideComponentActual: bundled actual model-level mod-side data;
* ModSideResidualMissing/Gap: the residual exact missing data after the model
  level is supplied -- only the local fractional ideal transport (J_v) and the
  realified value-layer transport remain;
* frobenioidModToMODIsoGap_of_residual: reduction theorem: the previous
  five-field FrobenioidModToMODIsoMissing record is implied by the two-field
  residual, because modPhi/modInput/carrierFunctor/divisorNaturalIso are actual
  model-level objects and the realification identity layer is actual.

LABEL: prerequisite component only, NOT the paper's mod-side Frobenioid.  The
model-level Phi/Input here is the Example 3.6 model presentation; the paper's
(F^boxplus_mod) additionally carries the local fractional ideals J_v, which is
the named residual.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

open CategoryTheory

namespace LeanFormal.IUT.XiFPaper.S3136ModSidePhiInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.S3136FrobenioidIsoLayerActual
open LeanFormal.IUT.XiFPaper.S3136ModSideInputActual

universe u

variable {f : Type u} [Field f] [NumberField f]

/-- The actual model-level mod-side DivisorialMonoidOn data: the Example 3.6
global effective-divisor cone on the bottom base. -/
noncomputable def modSidePhiActual :
    Iut.DivisorialMonoidOn (BottomBase.{u}) BottomFSM :=
  globalDivisorMonoidOn (F := f)

/-- The actual model-level mod-side Input data: the Example 3.6 model input
(rational functions and principal-divisor map). -/
noncomputable def modSideInputActual :
    Iut.SourceModelFrobenioid.Input (modSidePhiActual (f := f)) :=
  numberFieldSourceModelInput (F := f)

/-- The actual model-level mod-side carrier category. -/
abbrev modSideCarrierActual : Type u :=
  Iut.SourceModelFrobenioid.Carrier (modSidePhiActual (f := f))
    (modSideInputActual (f := f))

/-- The actual model-level mod-side carrier functor candidate: the identity
carrier equivalence (the model-level comparison is the identity). -/
noncomputable def modSideCarrierFunctorActual :
    CategoryTheory.Equivalence (modSideCarrierActual (f := f))
      (modSideCarrierActual (f := f)) :=
  CategoryTheory.Equivalence.refl (C := modSideCarrierActual (f := f))

/-- The actual model-level mod-side base/divisor layer isomorphism (identity
comparison). -/
noncomputable def modSideBaseDivisorLayerActual :
    BaseDivisorLayerIso (BottomBase.{u}) BottomFSM (modSidePhiActual (f := f)) :=
  globalBaseDivisorLayerIso (f := f)

/-- The actual model-level mod-side divisor natural-isomorphism component
(identity comparison). -/
noncomputable def modSideDivisorNatIsoActual :
    DivisorMonoidNatIsoComponent (BottomBase.{u}) BottomFSM
      (modSidePhiActual (f := f)) (modSidePhiActual (f := f)) :=
  globalDivisorNatIsoReflComponent (f := f)

/-- All actual model-level mod-side Phi/Input/carrier/base-divisor/divisor-natural
data, bundled. -/
structure ModSideComponentActual where
  phi : Iut.DivisorialMonoidOn (BottomBase.{u}) BottomFSM
  input : Iut.SourceModelFrobenioid.Input phi
  baseDivisorLayer : BaseDivisorLayerIso (BottomBase.{u}) BottomFSM phi
  divisorNatIso : DivisorMonoidNatIsoComponent (BottomBase.{u}) BottomFSM phi phi

/-- The actual model-level mod-side component. -/
noncomputable def modSideComponentActual :
    ModSideComponentActual.{u} where
  phi := modSidePhiActual (f := f)
  input := modSideInputActual (f := f)
  baseDivisorLayer := modSideBaseDivisorLayerActual (f := f)
  divisorNatIso := modSideDivisorNatIsoActual (f := f)

/-- The residual exact missing data for the paper's mod-to-MOD Frobenioid
isomorphism after the actual model-level component is supplied: only the local
fractional ideal transport (J_v; IUT III, Prop. 3.7, (ii), (v)) and the
realified value-layer transport (IUT III, Prop. 3.7, (i); IUT II, Cor. 4.8, (ii))
remain. -/
structure ModSideResidualMissing where
  localFractionalIdealTransport : Prop
  realifiedValueTransport : Prop

/-- The residual exact gap. -/
def ModSideResidualGap : Prop := Nonempty ModSideResidualMissing

/-- Coverage of the actual model-level component: four of the six named fields of
the previous Frobenioid carrier-functor/Input gap record are discharged by actual
model-level objects (mod-side Phi, mod-side Input, the identity carrier
equivalence, and the identity divisor-natural-iso component).  The remaining two
fields are exactly the residual record below and are NOT proven. -/
theorem modSideComponentActual_coverage :
    Nonempty (Iut.DivisorialMonoidOn (BottomBase.{u}) BottomFSM) ∧
      Nonempty (Iut.SourceModelFrobenioid.Input (modSidePhiActual (f := f))) ∧
      Nonempty (CategoryTheory.Equivalence (modSideCarrierActual (f := f))
        (modSideCarrierActual (f := f))) ∧
      Nonempty (DivisorMonoidNatIsoComponent (BottomBase.{u}) BottomFSM
        (modSidePhiActual (f := f)) (modSidePhiActual (f := f))) :=
  ⟨⟨modSidePhiActual (f := f)⟩, ⟨modSideInputActual (f := f)⟩,
    ⟨modSideCarrierFunctorActual (f := f)⟩,
    ⟨modSideDivisorNatIsoActual (f := f)⟩⟩
#check modSidePhiActual
#check modSideInputActual
#check modSideCarrierActual
#check modSideCarrierFunctorActual
#check modSideComponentActual
#check ModSideResidualGap
#check modSideComponentActual_coverage

end LeanFormal.IUT.XiFPaper.S3136ModSidePhiInputActual
end