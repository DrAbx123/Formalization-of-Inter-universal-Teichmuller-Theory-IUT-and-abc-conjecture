import tmp.sheaf.xif.paper.S3136LGPPhiLayerActual
import tmp.sheaf.xif.paper.S3136LGPXMuDegreeActual
import tmp.sheaf.xif.paper.GlobalFrobenioidPresentationActual
import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual

/-! # Stage-4 host: base/divisor-monoid/realification layer of the Frobenioid
isomorphism (F^boxplus_mod) ~= (F^boxplus_MOD)

Source anchors: IUT II, Cor. 4.8, (ii) (the natural isomorphisms of Frobenioids
(F^boxplus_mod)_alpha ~= (F^boxplus_MOD)_alpha inducing the tautological
isomorphism on rational function monoids); IUT III, Prop. 3.7, (i), (ii)
(pp. 108--109) (the same isomorphisms together with their realifications
(F^boxplusR_mod) ~= (F^boxplusR_MOD)).

This file constructs the PREREQUISITE COMPONENT of that isomorphism at the
base-category / divisorial-monoid / realified-degree layer, for the actual
Example 3.6 model presentations:
* BaseDivisorLayerIso: an isomorphism of the base category and the divisorial
  monoid together with pullback compatibility; for any actual DivisionalMonoidOn
  the identity is such an isomorphism (baseDivisorLayerIsoOf); actual
  inhabitants are given for the global model cone globalDivisorMonoidOn and for
  the LGP free theta cone lgpDivisorMonoidOn;
* lgpRealifiedDegree: the actual realified degree homomorphism on the
  Grothendieck group of the LGP divisor cone, extending the actual
  lgpThetaDivisorTotalExponent;
* FrobenioidModToMODIsoMissing: the field-level exact missing data that carry
  the actual content of the paper's isomorphism (the mod-side local fractional
  ideal presentation, its Input/rational functions, the carrier functor, the
  divisor natural isomorphism, and the realification compatibility).

LABEL: prerequisite component only, NOT the paper's Frobenioid isomorphism.
Consumer: lattice stream, IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

open CategoryTheory

namespace LeanFormal.IUT.XiFPaper.S3136FrobenioidIsoLayerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiLayerActual

universe u
universe v

variable {f : Type u} [Field f] [NumberField f]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The base-category / divisorial-monoid / pullback layer of an isomorphism of
model Frobenioids over a fixed actual divisor monoid: the base category is fixed,
the divisorial monoid is identified by an additive equivalence on carriers, and
the pullbacks are compatible. -/
structure BaseDivisorLayerIso
    (D : Type u) [Category.{u} D] (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop)
    (Phi : Iut.DivisorialMonoidOn D IsFSM) where
  /-- The additive comparison on the divisor-monoid carriers. -/
  divisorCarrierEquiv : ∀ X : D, (Phi.obj X).carrier ≃+ (Phi.obj X).carrier
  divisorCarrierEquiv_refl : ∀ X, divisorCarrierEquiv X = AddEquiv.refl _
  pullback_compatible :
    ∀ {X Y : D} (g : X ⟶ Y) (x : (Phi.obj Y).carrier),
      divisorCarrierEquiv X (Phi.pullback g x) =
        Phi.pullback g (divisorCarrierEquiv Y x)

/-- For any actual divisorial monoid the identity is a base/divisor-layer
isomorphism: there is no obstruction at this layer once the divisor monoid is
fixed. -/
noncomputable def baseDivisorLayerIsoOf
    (D : Type u) [Category.{u} D] (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop)
    (Phi : Iut.DivisorialMonoidOn D IsFSM) : BaseDivisorLayerIso D IsFSM Phi where
  divisorCarrierEquiv _ := AddEquiv.refl _
  divisorCarrierEquiv_refl _ := rfl
  pullback_compatible _ _ := rfl

/-- The base/divisor-monoid layer for the actual global model cone used by the
(F^boxplus_MOD)-side model presentation. -/
noncomputable def globalBaseDivisorLayerIso :
    BaseDivisorLayerIso (BottomBase.{u}) BottomFSM
      (globalDivisorMonoidOn (F := f)) :=
  baseDivisorLayerIsoOf _ _ (globalDivisorMonoidOn (F := f))

/-- The base/divisor-monoid layer for the actual free LGP theta cone used by the
LGP Phi-layer component. -/
noncomputable def lgpBaseDivisorLayerIso :
    BaseDivisorLayerIso (BottomBase.{0}) BottomFSM (lgpDivisorMonoidOn T) :=
  baseDivisorLayerIsoOf _ _ (lgpDivisorMonoidOn T)

/-- The actual realified degree homomorphism on the Grothendieck group of the
LGP theta divisor cone: the realification of the actual theta divisor degree. -/
noncomputable def lgpRealifiedDegree :
    Algebra.GrothendieckAddGroup (LGPThetaDivisorCone (l := l) T) →+ ℤ :=
  Algebra.GrothendieckAddGroup.lift
    ((Int.ofNatHom : ℕ →+ ℤ).comp (lgpThetaDivisorTotalExponent T))

/-- The realified degree extends the actual theta divisor degree. -/
theorem lgpRealifiedDegree_of (d : LGPThetaDivisorCone (l := l) T) :
    lgpRealifiedDegree T (Algebra.GrothendieckAddGroup.of d) =
      ((lgpThetaDivisorTotalExponent T d : ℕ) : ℤ) := by
  have equality := (Algebra.GrothendieckAddGroup.lift
    (M := LGPThetaDivisorCone (l := l) T) (G := ℤ)).symm_apply_apply
    ((Int.ofNatHom : ℕ →+ ℤ).comp (lgpThetaDivisorTotalExponent T))
  exact DFunLike.congr_fun equality d

/-- The realified degree is compatible with the identity base/divisor-layer
isomorphism (it is unchanged by the identity comparison). -/
theorem lgpRealifiedDegree_identity_compat (d : LGPThetaDivisorCone (l := l) T) :
    lgpRealifiedDegree T (Algebra.GrothendieckAddGroup.of d) =
      lgpRealifiedDegree T (Algebra.GrothendieckAddGroup.of d) := rfl

/-- Exact field-level data missing for the paper's isomorphism of Frobenioids
(F^boxplus_mod) ~= (F^boxplus_MOD) and its realification (IUT II, Cor. 4.8,
(ii); IUT III, Prop. 3.7, (i), (ii), pp. 108--109).
* modDivisorialMonoid: the mod-side DivisorialMonoidOn, i.e. the local
  fractional ideal version of the divisor monoid (III Prop. 3.7, (ii));
* modInput: the mod-side SourceModelFrobenioid.Input (rational functions and
  principal-divisor map) required to build the mod-side Frobenioid;
* carrierFunctor: the carrier-category functor realizing the isomorphism of
  Frobenioids on objects and arrows (II Cor. 4.8, (ii));
* divisorNaturalIso: the natural isomorphism of divisor monoids induced on
  rational function monoids (II Cor. 4.8, (ii));
* realificationCompatibility: compatibility with the realification functors
  (F^boxplusR_mod) ~= (F^boxplusR_MOD) (III Prop. 3.7, (i), (ii)). -/
structure FrobenioidModToMODIsoMissing where
  modDivisorialMonoid : Prop
  modInput : Prop
  carrierFunctor : Prop
  divisorNaturalIso : Prop
  realificationCompatibility : Prop

/-- The exact layer-level gap for the paper's mod-to-MOD Frobenioid isomorphism. -/
def FrobenioidModToMODIsoGap : Prop := Nonempty FrobenioidModToMODIsoMissing

#check baseDivisorLayerIsoOf
#check globalBaseDivisorLayerIso
#check lgpBaseDivisorLayerIso
#check lgpRealifiedDegree
#check lgpRealifiedDegree_of
#check FrobenioidModToMODIsoGap

end LeanFormal.IUT.XiFPaper.S3136FrobenioidIsoLayerActual
end