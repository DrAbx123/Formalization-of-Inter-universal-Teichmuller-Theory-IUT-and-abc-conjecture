import tmp.sheaf.xif.paper.S1951KummerEvaluationSquareActual
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitUnitsActionSupply

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

/-!
# S1967: O^×μ domain audit, reduced κ^×μ interface, and the exact first missing

Layer: O (original Theta-link / q-pilot), on the actual S1895 paper input.

## Status

**Missing** for the paper-level operation-level object.  This file does not
construct the group-theoretic O^×μ(G) of IUT II, Example 1.8, (iii), (iv), nor
the paper-level κ^×μ/evaluation isomorphism.  It does four things:

1. It constructs the reduced source-strip interface on the available S1895
   carrier: the O^× unit module, its O^×μ torsion quotient, actual
   KappaOrbitUnitsActionDatum inhabitants induced by the actual source links,
   the pair datum, the operation-level evaluation isomorphism, and the
   operation-level square.
2. It proves that the available S1895 carrier is unit-trivial: the value monoid
   of the S1487 shear strip is SourceHaarActualValueMonoid (the nonpositive
   reals under addition), whose unit group is trivial.  Consequently the
   reduced κ^×μ representatives above are identity completions in content, not
   the paper's arithmetic κ^×μ.
3. It constructs a genuine nontrivial local-field O^×μ(G) domain for
   G = LocalAbsoluteGalois p, with the actual Galois action, and proves that
   the local q-parameter p is not torsion, so this domain is nontrivial.
4. It proves that the available S1487 carrier cannot be identified with the
   actual local O^×μ: there is no multiplicative equivalence between the trivial
   S1487 units and the nontrivial local units, and no TimesMuKummer.Isomorphism
   from the local O^×μ to the trivial S1487 O^×μ.

The exact first missing is therefore not a missing proof about the existing
carriers; it is a missing carrier/construction: the actual local O^× modules
(or the group-theoretic algorithm producing them) are not attached to the
S1895 source input.  See the final section for the itemized gap.

## Constructed on the available carrier

* OUnits v is the actual unit group (LGP.Mon v)^x of the LGP source strip of
  the S1895 input; OUnitsAction v is the actual action of KummerGroup D.
* OUnitsMu v = TimesMuQuotient (OUnits v) is the torsion quotient, and
  OUnitsMuAction v is the descended action.
* envKappaDatum, gauKappaDatum, lgpLowerKappaDatum inhabit
  KappaOrbitUnitsActionDatum with source module OUnits and Kummer
  representatives induced by the actual source links fLinkAt 1 0 0 0,
  fLinkAt 1 0 0 1, and fLinkAt 1 0 1 1.  These are not literal
  TimesMuKummer.Isomorphism.refl terms, but because OUnits is trivial they are
  identity completions in content (proved in section 7).
* envGauPairDatum gives the two-strip form over the common O^×μ(G) domain.
  Its layerKummer is operationEvaluationIso, the operation-level evaluation
  isomorphism env -> gau factoring through the common domain.
* operationEvaluationIso_equiv_eq_xMu identifies its quotient equivalence with
  the actual strip-equivalence transport xMuQuotientEquiv (linkEnvToGau D).
* operationEvaluationIso_equiv_eq_upperEvaluation identifies it with S1951's
  reduced evaluation unit layer.
* operationSquare_commutes is the operation-level square
  env -> LGP -> lgp versus env -> gau -> lgp.

## Exact first missing (summary)

(a) The actual local-field O^× carrier for the S1895 source input.  The S1487
    strip uses SourceHaarActualValueMonoid, whose units are trivial; the paper's
    local O^× is a nontrivial group of local-field units.  The two cannot be
    identified (section 9).
(b) The group-theoretic algorithm G |-> O^×(G), G |-> O^×μ(G) of IUT II,
    Example 1.8, (iii), (iv), and its identification with the source modules.
(c) The split-Frobenioid identification Aut(‡A) ≅ G_w of IUT II, Definition
    4.9, (ii), with the 2l-torsion and splittings.
(d) The F^⊩ carrier and the theta/Gaussian monoids of IUT II, Corollary 4.6,
    (iv), (v), needed for the paper's Corollary 4.10, (ii), evaluation
    isomorphism.  The present evaluation isomorphism is only the reduced
    F^⊢ times-mu unit layer.
(e) The profinite topology: the existing source interface uses the indiscrete
    FPrimeStrip.productPiTopology fallback, not the paper's topology.

No Prop slot, empty type, arbitrary inhabitant, sorry or axiom is used.  The
missing objects are recorded as the existing interfaces they are; this file
does not fabricate an inhabitant for the group-theoretic algorithm.
-/

namespace LeanFormal.IUT.XiFPaper.S1967OUnitsMuActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open General

/-! ## 1. Composition of TimesMuKummer.Isomorphisms -/

namespace IsoAux

universe uG uU uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} [CommGroup U] {W : Type uW} [CommGroup W]
variable {X : Type uX} [CommGroup X]
variable {source : G →* MulAut U} {target : G →* MulAut W} {third : G →* MulAut X}

/-- The inverse of a TimesMuKummer.Isomorphism, with the transposed actions. -/
noncomputable def symm (κ : TimesMuKummer.Isomorphism source target) :
    TimesMuKummer.Isomorphism target source where
  equiv := κ.equiv.symm
  equivariant := by
    intro g x
    apply κ.equiv.injective
    rw [κ.equiv.apply_symm_apply, κ.equivariant, κ.equiv.apply_symm_apply]
  invariantImage := by
    intro H
    rw [← κ.invariantImage H]
    exact Equiv.symm_image_image κ.equiv.toEquiv _

/-- Composition of two TimesMuKummer.Isomorphisms. -/
noncomputable def trans (κ₁ : TimesMuKummer.Isomorphism source target)
    (κ₂ : TimesMuKummer.Isomorphism target third) :
    TimesMuKummer.Isomorphism source third where
  equiv := κ₁.equiv.trans κ₂.equiv
  equivariant := by
    intro g x
    change κ₂.equiv (κ₁.equiv (TimesMuQuotient.action source g x)) =
      TimesMuQuotient.action third g (κ₂.equiv (κ₁.equiv x))
    rw [κ₁.equivariant, κ₂.equivariant]
  invariantImage := by
    intro H
    rw [MulEquiv.coe_trans, Set.image_comp]
    rw [κ₁.invariantImage H, κ₂.invariantImage H]

end IsoAux

/-! ## 2. The O^× module and its O^×μ quotient on the available carrier -/

variable (D : S1895PaperInput)

/-- The unit group of the LGP source strip.  On the S1895 input this is the
unit group of the S1487 value monoid SourceHaarActualValueMonoid; it is trivial
(proved in section 7), so it is not the paper's local-field O^× module. -/
noncomputable abbrev OUnits (v : PaperV) : Type :=
  ((lgpStrip D).Mon v)ˣ

/-- The actual action of the common group on the source unit module. -/
noncomputable abbrev OUnitsAction (v : PaperV) :
    KummerGroup D →* MulAut (OUnits D v) :=
  ((lgpStrip D).unitsAction v).comp (factorLGP D v)

/-- The torsion quotient of the source unit module. -/
noncomputable abbrev OUnitsMu (v : PaperV) : Type :=
  TimesMuQuotient (OUnits D v)

/-- The descended action on the O^×μ quotient. -/
noncomputable abbrev OUnitsMuAction (v : PaperV) :
    KummerGroup D →* MulAut (OUnitsMu D v) :=
  TimesMuQuotient.action (OUnitsAction D v)

@[simp] theorem OUnitsMuAction_quotientMap
    (v : PaperV) (g : KummerGroup D) (u : OUnits D v) :
    OUnitsMuAction D v g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (OUnitsAction D v g u) := rfl

/-- The O^×μ action is the LGP strip's timesMuAction, precomposed with the
evaluation factor. -/
theorem OUnitsMuAction_eq_lgp_timesMu (v : PaperV) :
    OUnitsMuAction D v =
      ((lgpStrip D).timesMuAction v).comp (factorLGP D v) := rfl

/-! ## 3. Reduced κ^×μ layers from the actual source links -/

noncomputable abbrev envFactor (v : PaperV) :
    KummerGroup D →* (envStrip D).toDPrimeStrip.Pi v :=
  factorLowerOfEquiv (linkLGPToEnv D) (factorLGP D) v

noncomputable abbrev gauFactor (v : PaperV) :
    KummerGroup D →* (gauStrip D).toDPrimeStrip.Pi v :=
  factorLowerOfEquiv (linkLGPToGau D) (factorLGP D) v

noncomputable abbrev lgpLowerFactor (v : PaperV) :
    KummerGroup D →* (lgpLowerStrip D).toDPrimeStrip.Pi v :=
  factorLowerOfEquiv (linkLGPToLgpLower D) (factorLGP D) v

noncomputable abbrev envKappaLayer :
    SourceTimesMuKummerLayer (KummerGroup D) (lgpStrip D) (envStrip D) :=
  layerOfFactors (G := KummerGroup D) (linkLGPToEnv D) (factorLGP D)

noncomputable abbrev gauKappaLayer :
    SourceTimesMuKummerLayer (KummerGroup D) (lgpStrip D) (gauStrip D) :=
  layerOfFactors (G := KummerGroup D) (linkLGPToGau D) (factorLGP D)

noncomputable abbrev lgpLowerKappaLayer :
    SourceTimesMuKummerLayer (KummerGroup D) (lgpStrip D) (lgpLowerStrip D) :=
  layerOfFactors (G := KummerGroup D) (linkLGPToLgpLower D) (factorLGP D)

@[simp] theorem envKappaLayer_sourceAction (v : PaperV) :
    (envKappaLayer D).sourceAction v = OUnitsAction D v := rfl

@[simp] theorem envKappaLayer_targetAction (v : PaperV) :
    (envKappaLayer D).targetAction v =
      ((envStrip D).unitsAction v).comp (envFactor D v) := rfl

@[simp] theorem envKappaLayer_kummer (v : PaperV) :
    (envKappaLayer D).kummer v =
      kummerIsoOfFactors (G := KummerGroup D) (linkLGPToEnv D)
        (factorLGP D) v := rfl

@[simp] theorem gauKappaLayer_sourceAction (v : PaperV) :
    (gauKappaLayer D).sourceAction v = OUnitsAction D v := rfl

@[simp] theorem lgpLowerKappaLayer_sourceAction (v : PaperV) :
    (lgpLowerKappaLayer D).sourceAction v = OUnitsAction D v := rfl

/-- Pointwise formula for the env representative: the quotient-unit transport
of the source link fLinkAt 1 0 0 0. -/
theorem envKappaLayer_kummer_equiv_apply (v : PaperV) (u : OUnits D v) :
    ((envKappaLayer D).kummer v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        (Units.mapEquiv ((linkLGPToEnv D).isoMon v) u) := by
  change (xMuQuotientEquiv (linkLGPToEnv D) v)
      (TimesMuQuotient.quotientMap u) =
    TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkLGPToEnv D).isoMon v) u)
  change quotientUnitsEquiv (Units.mapEquiv ((linkLGPToEnv D).isoMon v))
      (TimesMuQuotient.quotientMap u) =
    TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkLGPToEnv D).isoMon v) u)
  exact quotientUnitsEquiv_quotientMap _ u

/-! ## 4. Reduced KappaOrbitUnitsActionDatum inhabitants -/

noncomputable def envKappaDatum :
    KappaOrbitUnitsActionDatum (KummerGroup D) (envStrip D) where
  sourceUnits := OUnits D
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := OUnitsAction D
  factor := envFactor D
  kappa := fun v => (envKappaLayer D).kummer v

noncomputable def gauKappaDatum :
    KappaOrbitUnitsActionDatum (KummerGroup D) (gauStrip D) where
  sourceUnits := OUnits D
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := OUnitsAction D
  factor := gauFactor D
  kappa := fun v => (gauKappaLayer D).kummer v

noncomputable def lgpLowerKappaDatum :
    KappaOrbitUnitsActionDatum (KummerGroup D) (lgpLowerStrip D) where
  sourceUnits := OUnits D
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := OUnitsAction D
  factor := lgpLowerFactor D
  kappa := fun v => (lgpLowerKappaLayer D).kummer v

@[simp] theorem envKappaDatum_sourceUnits (v : PaperV) :
    (envKappaDatum D).sourceUnits v = OUnits D v := rfl

@[simp] theorem envKappaDatum_sourceAction (v : PaperV) :
    (envKappaDatum D).sourceAction v = OUnitsAction D v := rfl

@[simp] theorem envKappaDatum_factor (v : PaperV) :
    (envKappaDatum D).factor v = envFactor D v := rfl

@[simp] theorem envKappaDatum_kappa (v : PaperV) :
    (envKappaDatum D).kappa v = (envKappaLayer D).kummer v := rfl

@[simp] theorem gauKappaDatum_kappa (v : PaperV) :
    (gauKappaDatum D).kappa v = (gauKappaLayer D).kummer v := rfl

@[simp] theorem lgpLowerKappaDatum_kappa (v : PaperV) :
    (lgpLowerKappaDatum D).kappa v = (lgpLowerKappaLayer D).kummer v := rfl

theorem envKappaDatum_kappa_equiv_apply (v : PaperV) (u : OUnits D v) :
    ((envKappaDatum D).kappa v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        (Units.mapEquiv ((linkLGPToEnv D).isoMon v) u) :=
  envKappaLayer_kummer_equiv_apply D v u

theorem gauKappaDatum_kappa_equiv_apply (v : PaperV) (u : OUnits D v) :
    ((gauKappaDatum D).kappa v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        (Units.mapEquiv ((linkLGPToGau D).isoMon v) u) := by
  rw [gauKappaDatum_kappa]
  change (xMuQuotientEquiv (linkLGPToGau D) v)
      (TimesMuQuotient.quotientMap u) =
    TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkLGPToGau D).isoMon v) u)
  change quotientUnitsEquiv (Units.mapEquiv ((linkLGPToGau D).isoMon v))
      (TimesMuQuotient.quotientMap u) =
    TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkLGPToGau D).isoMon v) u)
  exact quotientUnitsEquiv_quotientMap _ u

theorem lgpLowerKappaDatum_kappa_equiv_apply (v : PaperV) (u : OUnits D v) :
    ((lgpLowerKappaDatum D).kappa v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        (Units.mapEquiv ((linkLGPToLgpLower D).isoMon v) u) := by
  rw [lgpLowerKappaDatum_kappa]
  change (xMuQuotientEquiv (linkLGPToLgpLower D) v)
      (TimesMuQuotient.quotientMap u) =
    TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkLGPToLgpLower D).isoMon v) u)
  change quotientUnitsEquiv (Units.mapEquiv ((linkLGPToLgpLower D).isoMon v))
      (TimesMuQuotient.quotientMap u) =
    TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkLGPToLgpLower D).isoMon v) u)
  exact quotientUnitsEquiv_quotientMap _ u

/-! ## 5. The pair datum and the reduced evaluation isomorphism -/

noncomputable def envGauPairDatum :
    KappaOrbitUnitsActionPairDatum (KummerGroup D) (envStrip D) (gauStrip D) where
  sourceUnits := OUnits D
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := OUnitsAction D
  factorUpper := envFactor D
  factorLower := gauFactor D
  kappaUpper := fun v => (envKappaLayer D).kummer v
  kappaLower := fun v => (gauKappaLayer D).kummer v

@[simp] theorem envGauPairDatum_kappaUpper (v : PaperV) :
    (envGauPairDatum D).kappaUpper v = (envKappaLayer D).kummer v := rfl

@[simp] theorem envGauPairDatum_kappaLower (v : PaperV) :
    (envGauPairDatum D).kappaLower v = (gauKappaLayer D).kummer v := rfl

noncomputable abbrev operationEvaluationIso (v : PaperV) :
    TimesMuKummer.Isomorphism
      (((envStrip D).unitsAction v).comp (envFactor D v))
      (((gauStrip D).unitsAction v).comp (gauFactor D v)) :=
  (envGauPairDatum D).layerKummer v

theorem operationEvaluationIso_eq_commonDomain (v : PaperV) :
    operationEvaluationIso D v =
      IsoAux.trans (IsoAux.symm ((envKappaLayer D).kummer v))
        ((gauKappaLayer D).kummer v) := by
  apply TimesMuKummer.Isomorphism.ext
  rfl

theorem linkLGPToGau_eq_trans :
    linkLGPToGau D =
      FPrimeStripEquiv.trans (linkLGPToEnv D) (linkEnvToGau D) := by
  unfold linkLGPToGau linkLGPToEnv linkEnvToGau
  exact ((paperInput D).fLinkAt_trans 1 0 0 0 0 1).symm

theorem units_transport_linkLGPToGau (v : PaperV) (u : OUnits D v) :
    Units.mapEquiv ((linkLGPToGau D).isoMon v)
        ((Units.mapEquiv ((linkLGPToEnv D).isoMon v)).symm u) =
      Units.mapEquiv ((linkEnvToGau D).isoMon v) u := by
  rw [linkLGPToGau_eq_trans]
  rfl

theorem operationEvaluationIso_equiv_eq_xMu (v : PaperV) :
    (operationEvaluationIso D v).equiv =
      xMuQuotientEquiv (linkEnvToGau D) v := by
  apply MulEquiv.ext
  intro x
  obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
  change ((envGauPairDatum D).layerKummer v).equiv
      (TimesMuQuotient.quotientMap u) =
    (xMuQuotientEquiv (linkEnvToGau D) v)
      (TimesMuQuotient.quotientMap u)
  rw [KappaOrbitUnitsActionPairDatum.layerKummer]
  change TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkLGPToGau D).isoMon v)
        ((Units.mapEquiv ((linkLGPToEnv D).isoMon v)).symm u)) =
    TimesMuQuotient.quotientMap
      (Units.mapEquiv ((linkEnvToGau D).isoMon v) u)
  rw [units_transport_linkLGPToGau]

theorem operationEvaluationIso_equiv_eq_upperEvaluation (v : PaperV) :
    (operationEvaluationIso D v).equiv =
      (upperEvaluation D).unitPortion.unitLayer v := by
  rw [operationEvaluationIso_equiv_eq_xMu]
  rfl

noncomputable def operationEvaluationLayer :
    SourceTimesMuKummerLayer (KummerGroup D) (envStrip D) (gauStrip D) where
  sourceAction := fun v => ((envStrip D).unitsAction v).comp (envFactor D v)
  targetAction := fun v => ((gauStrip D).unitsAction v).comp (gauFactor D v)
  kummer := operationEvaluationIso D

@[simp] theorem operationEvaluationLayer_kummer (v : PaperV) :
    (operationEvaluationLayer D).kummer v = operationEvaluationIso D v := rfl

/-! ## 6. The reduced operation-level square -/

noncomputable def operationLeftKummer (v : PaperV) :
    TimesMuKummer.Isomorphism
      (((envStrip D).unitsAction v).comp (envFactor D v))
      (OUnitsAction D v) :=
  IsoAux.symm ((envKappaLayer D).kummer v)

noncomputable def operationLowerHorizontal (v : PaperV) :
    TimesMuKummer.Isomorphism
      (OUnitsAction D v)
      (((lgpLowerStrip D).unitsAction v).comp (lgpLowerFactor D v)) :=
  (lgpLowerKappaLayer D).kummer v

noncomputable def operationRightKummer (v : PaperV) :
    TimesMuKummer.Isomorphism
      (((gauStrip D).unitsAction v).comp (gauFactor D v))
      (((lgpLowerStrip D).unitsAction v).comp (lgpLowerFactor D v)) :=
  IsoAux.trans (IsoAux.symm ((gauKappaLayer D).kummer v))
    ((lgpLowerKappaLayer D).kummer v)

theorem operationSquare_commutes (v : PaperV) :
    IsoAux.trans (operationLeftKummer D v) (operationLowerHorizontal D v) =
      IsoAux.trans (operationEvaluationIso D v) (operationRightKummer D v) := by
  apply TimesMuKummer.Isomorphism.ext
  apply MulEquiv.ext
  intro x
  change ((lgpLowerKappaLayer D).kummer v).equiv
      (((envKappaLayer D).kummer v).equiv.symm x) =
    ((lgpLowerKappaLayer D).kummer v).equiv
      (((gauKappaLayer D).kummer v).equiv.symm
        (((gauKappaLayer D).kummer v).equiv
          (((envKappaLayer D).kummer v).equiv.symm x)))
  rw [MulEquiv.symm_apply_apply]

/-! ## 7. The available S1895 carrier is unit-trivial

The S1895 input is built on the S1487 shear strip, whose value monoid is
SourceHaarActualValueMonoid, the additive monoid of nonpositive reals.  Its
unit group is trivial: an invertible element and its inverse are both
nonpositive, so both are zero.  Hence OUnits and OUnitsMu are trivial, and the
reduced κ^×μ representatives above are identity completions in content. -/

/-- The unit group of the S1487 value monoid is trivial. -/
theorem sourceHaarActualValueMonoid_units_subsingleton :
    Subsingleton (SourceHaarActualValueMonoid)ˣ := by
  constructor
  intro a b
  have key : ∀ u : (SourceHaarActualValueMonoid)ˣ, u = 1 := by
    intro u
    let M := SourceHaarActualValueMonoid
    let x : sourceHaarActualNonpositiveAddSubmonoid := Multiplicative.toAdd (u : M)
    let y : sourceHaarActualNonpositiveAddSubmonoid :=
      Multiplicative.toAdd ((u⁻¹ : (M)ˣ) : M)
    have hx : (x : ℝ) ≤ 0 := x.property
    have hy : (y : ℝ) ≤ 0 := y.property
    have hmul : (u : M) * ((u⁻¹ : (M)ˣ) : M) = 1 :=
      congrArg Units.val (mul_inv_cancel u)
    have h := congrArg (fun z : M =>
      (Multiplicative.toAdd z : sourceHaarActualNonpositiveAddSubmonoid)) hmul
    change x + y = 0 at h
    have hsum : (x : ℝ) + (y : ℝ) = 0 := by
      exact congrArg (fun z : sourceHaarActualNonpositiveAddSubmonoid => (z : ℝ)) h
    have hx0 : (x : ℝ) = 0 := by linarith
    apply Units.ext
    apply Multiplicative.ext
    apply Subtype.ext
    exact hx0
  rw [key a, key b]

/-- A torsion quotient of a subsingleton commutative group is subsingleton. -/
theorem timesMuQuotient_subsingleton_of_subsingleton
    {U : Type*} [CommGroup U] [Subsingleton U] :
    Subsingleton (TimesMuQuotient U) :=
  Quotient.instSubsingletonQuotient (QuotientGroup.leftRel (CommGroup.torsion U))

/-- The LGP strip's unit group is trivial. -/
theorem OUnits_subsingleton (v : PaperV) : Subsingleton (OUnits D v) := by
  change Subsingleton (SourceHaarActualValueMonoid)ˣ
  exact sourceHaarActualValueMonoid_units_subsingleton

/-- The reduced O^×μ domain is trivial. -/
theorem OUnitsMu_subsingleton (v : PaperV) : Subsingleton (OUnitsMu D v) := by
  haveI : Subsingleton (OUnits D v) := OUnits_subsingleton D v
  exact timesMuQuotient_subsingleton_of_subsingleton

/-- The env strip's unit group is also trivial. -/
theorem envUnits_subsingleton (v : PaperV) :
    Subsingleton ((envStrip D).Mon v)ˣ := by
  change Subsingleton (SourceHaarActualValueMonoid)ˣ
  exact sourceHaarActualValueMonoid_units_subsingleton

/-- The reduced env representative is the identity on the (trivial) quotient. -/
theorem envKappaDatum_kappa_equiv_trivial (v : PaperV) (x : OUnitsMu D v) :
    ((envKappaDatum D).kappa v).equiv x = x := by
  haveI : Subsingleton ((envStrip D).Mon v)ˣ := envUnits_subsingleton D v
  haveI : Subsingleton (TimesMuQuotient ((envStrip D).Mon v)ˣ) :=
    timesMuQuotient_subsingleton_of_subsingleton
  exact Subsingleton.elim _ _

/-! ## 8. A genuine nontrivial local-field O^×μ(G) domain -/

/-- The actual local unit group of the algebraic closure of Q_p. -/
noncomputable abbrev LocalOUnits (p : Nat) [Fact (Nat.Prime p)] : Type :=
  (AlgebraicClosure ℚ_[p])ˣ

/-- Its O^×μ quotient. -/
noncomputable abbrev LocalOUnitsMu (p : Nat) [Fact (Nat.Prime p)] : Type :=
  TimesMuQuotient (LocalOUnits p)

/-- The actual action of the local absolute Galois group. -/
noncomputable def LocalOUnitsAction (p : Nat) [Fact (Nat.Prime p)] :
    LocalAbsoluteGalois p →* MulAut (LocalOUnits p) :=
  localGaloisUnitsAction p

/-- The descended action on the local O^×μ quotient. -/
noncomputable def LocalOUnitsMuAction (p : Nat) [Fact (Nat.Prime p)] :
    LocalAbsoluteGalois p →* MulAut (LocalOUnitsMu p) :=
  TimesMuQuotient.action (LocalOUnitsAction p)

@[simp] theorem LocalOUnitsMuAction_quotientMap
    (p : Nat) [Fact (Nat.Prime p)]
    (g : LocalAbsoluteGalois p) (u : LocalOUnits p) :
    LocalOUnitsMuAction p g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (LocalOUnitsAction p g u) := rfl

/-- The local q-parameter p is not torsion in the local unit group. -/
theorem localQParameterFor_not_isOfFinOrder (p : Nat) [Fact (Nat.Prime p)] :
    ¬ IsOfFinOrder (localQParameterFor p : LocalOUnits p) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hnpos, hpow⟩
  have hval : ((localQParameterFor p : LocalOUnits p) :
      AlgebraicClosure ℚ_[p]) ^ n = 1 := by
    simpa using congrArg (fun z : LocalOUnits p =>
      (z : AlgebraicClosure ℚ_[p])) hpow
  have hnorm : ‖((localQParameterFor p : LocalOUnits p) :
      AlgebraicClosure ℚ_[p])‖ ^ n = 1 := by
    simpa using congrArg norm hval
  rw [localQParameterFor_norm_eq_inv] at hnorm
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hbase_nonneg : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hbase_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hlt : ((p : ℝ)⁻¹) ^ n < 1 :=
    pow_lt_one₀ hbase_nonneg hbase_lt hnpos.ne'
  nlinarith

/-- p is a nontrivial local unit. -/
theorem localQParameterFor_units_ne_one (p : Nat) [Fact (Nat.Prime p)] :
    (localQParameterFor p : LocalOUnits p) ≠ 1 := by
  have h := localQParameter_ne_one (⟨p, Fact.out⟩ : RationalPrimePlace)
  simpa [localQParameter, LocalOUnits] using h

/-- The local O^×μ quotient is nontrivial. -/
theorem localQParameterFor_quotient_ne_one (p : Nat) [Fact (Nat.Prime p)] :
    TimesMuQuotient.quotientMap (localQParameterFor p) ≠ 1 := by
  intro h
  apply localQParameterFor_not_isOfFinOrder p
  have hmem : (localQParameterFor p : LocalOUnits p) ∈
      MonoidHom.ker (TimesMuQuotient.quotientMap (U := LocalOUnits p)) :=
    MonoidHom.mem_ker.mpr h
  have htors : (localQParameterFor p : LocalOUnits p) ∈
      CommGroup.torsion (LocalOUnits p) := by
    simpa [TimesMuQuotient.quotientMap_ker] using hmem
  exact (CommGroup.mem_torsion _).mp htors

/-- The local O^×μ domain is nontrivial, hence is not the trivial S1487
carrier. -/
theorem LocalOUnitsMu_nontrivial (p : Nat) [Fact (Nat.Prime p)] :
    (TimesMuQuotient.quotientMap (localQParameterFor p) : LocalOUnitsMu p) ≠ 1 :=
  localQParameterFor_quotient_ne_one p

/-! ## 9. The reduced S1487 carrier cannot be identified with the local domain -/

/-- No multiplicative equivalence between the trivial S1487 units and the
nontrivial local units. -/
theorem no_units_equiv_sourceHaar_local (p : Nat) [Fact (Nat.Prime p)] :
    ¬ Nonempty ((SourceHaarActualValueMonoid)ˣ ≃* LocalOUnits p) := by
  rintro ⟨e⟩
  have hsub : Subsingleton (SourceHaarActualValueMonoid)ˣ :=
    sourceHaarActualValueMonoid_units_subsingleton
  obtain ⟨a, ha⟩ := e.surjective (localQParameterFor p)
  have ha1 : a = 1 := hsub.elim a 1
  have hmap : e a = 1 := by rw [ha1, map_one]
  exact localQParameterFor_units_ne_one p (ha.symm.trans hmap)

/-- At every place, the S1895 LGP unit group is not equivalent to the local
O^× unit group. -/
theorem no_s1895_units_equiv_local (v : PaperV) (p : Nat) [Fact (Nat.Prime p)] :
    ¬ Nonempty (OUnits D v ≃* LocalOUnits p) := by
  change ¬ Nonempty ((SourceHaarActualValueMonoid)ˣ ≃* LocalOUnits p)
  exact no_units_equiv_sourceHaar_local p

/-- There is no TimesMuKummer.Isomorphism from the local O^×μ module (with any
source action) to the trivial S1487 O^×μ module (with any target action): the
local quotient has a nontrivial element while the target quotient is a
subsingleton. -/
theorem no_local_to_sourceHaar_timesMuIso (p : Nat) [Fact (Nat.Prime p)]
    (rho : LocalAbsoluteGalois p →* MulAut (LocalOUnits p))
    (sigma : LocalAbsoluteGalois p →* MulAut ((SourceHaarActualValueMonoid)ˣ)) :
    ¬ Nonempty (TimesMuKummer.Isomorphism rho sigma) := by
  rintro ⟨κ⟩
  haveI : Subsingleton ((SourceHaarActualValueMonoid)ˣ) :=
    sourceHaarActualValueMonoid_units_subsingleton
  haveI : Subsingleton (TimesMuQuotient ((SourceHaarActualValueMonoid)ˣ)) :=
    timesMuQuotient_subsingleton_of_subsingleton
  have htriv : κ.equiv
      (TimesMuQuotient.quotientMap (localQParameterFor p)) = 1 :=
    Subsingleton.elim _ _
  have hpre : TimesMuQuotient.quotientMap
      (localQParameterFor p : LocalOUnits p) = 1 := by
    apply κ.equiv.injective
    rw [htriv, map_one]
  exact localQParameterFor_quotient_ne_one p hpre

/-! ## 10. The exact first missing -/

/- The positive content above is a reduced-carrier interface and a local-field
model, not the paper's operation-level object.  The first missing object is the
actual local-field O^× carrier on the S1895 source input, i.e. the replacement
of the S1487 value monoid by the local field units, together with the
group-theoretic algorithm of IUT II, Example 1.8, (iii), (iv), producing
O^×(G) and O^×μ(G) from G.  The local model in section 8 shows what the target
module is; section 9 proves that it cannot be identified with the available
S1487 carrier.

The remaining missing items are itemized in the module docstring:
(b) the group-theoretic algorithm and its identification with the source
    modules;
(c) the split-Frobenioid identification Aut(‡A) ≅ G_w of Definition 4.9, (ii);
(d) the F^⊩ carrier and theta/Gaussian monoids for Corollary 4.10, (ii);
(e) the profinite topology and the ind-topological structure.

No inhabitant for any of these is introduced here. -/

#check KappaOrbitUnitsActionDatum
#check KappaOrbitUnitsActionPairDatum
#check KappaOrbitUnitsActionDatum.structureOrbit
#check KappaOrbitUnitsActionDatum.representativeDifference_isKummerIsometry
#check upperEvaluation

/-! ## 11. Axiom probes -/

#print axioms OUnitsMuAction
#print axioms envKappaDatum
#print axioms gauKappaDatum
#print axioms lgpLowerKappaDatum
#print axioms envGauPairDatum
#print axioms operationEvaluationIso_equiv_eq_xMu
#print axioms operationEvaluationIso_equiv_eq_upperEvaluation
#print axioms operationSquare_commutes
#print axioms sourceHaarActualValueMonoid_units_subsingleton
#print axioms OUnits_subsingleton
#print axioms OUnitsMu_subsingleton
#print axioms envKappaDatum_kappa_equiv_trivial
#print axioms localQParameterFor_not_isOfFinOrder
#print axioms localQParameterFor_quotient_ne_one
#print axioms LocalOUnitsMu_nontrivial
#print axioms no_units_equiv_sourceHaar_local
#print axioms no_s1895_units_equiv_local
#print axioms no_local_to_sourceHaar_timesMuIso

end LeanFormal.IUT.XiFPaper.S1967OUnitsMuActual
