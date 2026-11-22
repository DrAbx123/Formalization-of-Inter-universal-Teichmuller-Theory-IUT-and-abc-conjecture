import tmp.sheaf.xif.paper.S3136FrobenioidIsoLayerActual

/-! # Stage-4 host: mod-side divisor natural isomorphism component and carrier functor gap

Source anchors: IUT II, Cor. 4.8, (ii) (the natural isomorphism of Frobenioids
(F^boxplus_mod)_alpha ~= (F^boxplus_MOD)_alpha, inducing the tautological
isomorphism on rational function monoids); IUT III, Prop. 3.7, (i), (ii)
(pp. 108--109) for the realified version.

The base/divisor/realification layer is already actual (previous file).  This
file adds the PREREQUISITE COMPONENT at the next layer:
* DivisorMonoidNatIsoComponent: a component-level natural isomorphism between
  two actual DivisorialMonoidOn data (additive carrier equivalences plus
  pullback naturality) - this is the shape of the divisor-natural-isomorphism
  field of the paper's Frobenioid isomorphism;
* divisorialNatIsoReflComponent: the identity component for any actual
  DivisorialMonoidOn (no obstruction at this component once Phi is fixed);
* modSideDivisorNatIsoComponent: given the missing mod-side DivisorialMonoidOn
  data with its carrier comparison, the component is produced conditionally;
* FrobenioidCarrierFunctorMissing: the exact field-level missing data for the
  carrier functor / Input component (mod-side Input, functor on objects and
  homs, divisor natural isomorphism, balance compatibility; II Cor. 4.8, (ii),
  III Prop. 3.7, (i), (ii)).

LABEL: prerequisite component only, NOT the paper's Frobenioid isomorphism.
Consumer: lattice stream, IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

open CategoryTheory

namespace LeanFormal.IUT.XiFPaper.S3136ModSideInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiLayerActual

universe u

/-- Component-level natural isomorphism between two actual divisorial monoids
on the same base category: additive carrier equivalences plus pullback
naturality.  This is exactly the shape of the divisor-natural-isomorphism field
of a Frobenioid isomorphism (IUT II, Cor. 4.8, (ii)). -/
structure DivisorMonoidNatIsoComponent
    (D : Type u) [Category.{u} D] (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop)
    (Phi₁ Phi₂ : Iut.DivisorialMonoidOn D IsFSM) where
  /-- The additive comparison on divisor-monoid carriers. -/
  app : ∀ X : D, (Phi₁.obj X).carrier ≃+ (Phi₂.obj X).carrier
  /-- Naturality with respect to the pullbacks. -/
  natural : ∀ {X Y : D} (g : X ⟶ Y) (x : (Phi₁.obj Y).carrier),
    app X (Phi₁.pullback g x) = Phi₂.pullback g (app Y x)

/-- The identity component: for any actual DivisorialMonoidOn there is a
natural-isomorphism component on the divisor monoids (no obstruction once Phi
is fixed). -/
noncomputable def divisorialNatIsoReflComponent
    (D : Type u) [Category.{u} D] (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop)
    (Phi : Iut.DivisorialMonoidOn D IsFSM) :
    DivisorMonoidNatIsoComponent D IsFSM Phi Phi where
  app _ := AddEquiv.refl _
  natural _ _ := rfl

/-- The identity component for the actual global model divisor monoid. -/
noncomputable def globalDivisorNatIsoReflComponent
    {f : Type u} [Field f] [NumberField f] :
    DivisorMonoidNatIsoComponent (BottomBase.{u}) BottomFSM
      (globalDivisorMonoidOn (F := f)) (globalDivisorMonoidOn (F := f)) :=
  divisorialNatIsoReflComponent _ _ (globalDivisorMonoidOn (F := f))

/-- The identity component for the actual LGP free theta cone. -/
noncomputable def lgpDivisorNatIsoReflComponent
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    DivisorMonoidNatIsoComponent (BottomBase.{0}) BottomFSM
      (lgpDivisorMonoidOn T) (lgpDivisorMonoidOn T) :=
  divisorialNatIsoReflComponent _ _ (lgpDivisorMonoidOn T)

/-- Conditional component: given the mod-side DivisorialMonoidOn data and an
actual carrier comparison to the MODEL-side divisor monoid, the divisor
natural-isomorphism component is produced (this is the reduction of the
paper's field to the exact missing data). -/
noncomputable def modSideDivisorNatIsoComponent
    {f : Type u} [Field f] [NumberField f]
    (Phi_mod : Iut.DivisorialMonoidOn (BottomBase.{u}) BottomFSM)
    (e : ∀ X : BottomBase.{u},
      (Phi_mod.obj X).carrier ≃+ ((globalDivisorMonoidOn (F := f)).obj X).carrier)
    (hnat : ∀ {X Y : BottomBase.{u}} (g : X ⟶ Y)
      (x : (Phi_mod.obj Y).carrier),
      e X (Phi_mod.pullback g x) = (globalDivisorMonoidOn (F := f)).pullback g (e Y x)) :
    DivisorMonoidNatIsoComponent (BottomBase.{u}) BottomFSM Phi_mod
      (globalDivisorMonoidOn (F := f)) where
  app := e
  natural := hnat

/-- Exact field-level data missing for the mod-side Input / carrier functor
component of the paper's isomorphism (F^boxplus_mod) ~= (F^boxplus_MOD)
(IUT II, Cor. 4.8, (ii); IUT III, Prop. 3.7, (i), (ii), pp. 108--109).
* modPhi: the mod-side DivisorialMonoidOn (the local fractional ideal version,
  III Prop. 3.7, (ii));
* modInput: the mod-side SourceModelFrobenioid.Input (rational functions and
  principal-divisor map) building the mod-side Frobenioid;
* carrierFunctorObjects: the carrier-category functor on objects;
* carrierFunctorHoms: the carrier-category functor on arrows, compatible with
  the balance equation of the model Frobenioid arrows;
* divisorNaturalIso: the divisor natural isomorphism component (produced from
  the candidate data above);
* realificationCompatibility: compatibility with the realification functors
  (III Prop. 3.7, (i), (ii)). -/
structure FrobenioidCarrierFunctorMissing where
  modPhi : Prop
  modInput : Prop
  carrierFunctorObjects : Prop
  carrierFunctorHoms : Prop
  divisorNaturalIso : Prop
  realificationCompatibility : Prop

/-- The exact carrier-functor/Input gap. -/
def FrobenioidCarrierFunctorGap : Prop := Nonempty FrobenioidCarrierFunctorMissing

#check divisorialNatIsoReflComponent
#check globalDivisorNatIsoReflComponent
#check lgpDivisorNatIsoReflComponent
#check modSideDivisorNatIsoComponent
#check FrobenioidCarrierFunctorGap

end LeanFormal.IUT.XiFPaper.S3136ModSideInputActual
end