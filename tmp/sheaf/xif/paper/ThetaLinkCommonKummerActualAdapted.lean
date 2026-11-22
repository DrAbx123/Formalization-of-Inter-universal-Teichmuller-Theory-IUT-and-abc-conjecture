import tmp.sheaf.xif.paper.ThetaLinkKummerObjectsActualAdapted
import tmp.sheaf.xif.paper.ThetaLinkProfiniteTopologyActualAdapted
import tmp.sheaf.xif.paper.IPLAPTActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceKummerEvaluationSquareExtension

/-!
# Common topological Kummer layers for the four-corner Theta-link

The common abstract four-corner group

  CommonG = (v : V) -> S00.Pi v x S01.Pi v x S10.Pi v x S11.Pi v

is equipped with the profinite-completion topology (the initial topology from
its actual profinite completion).  On this actual topological group we construct
the Kummer layers from the actual strip equivalences and the actual local units
actions, using the common factor maps to each strip.

Then the four actual source arrows are assembled into
SourceKummerEvaluationSquare.ofThreeLegs and KummerEvaluationActual.

The IPL factorization equality itself remains an exact missing field: the square
produced by ofThreeLegs has its lower horizontal constructed from the upper leg,
so its commutation is actual, but the identification with the paper's actual
input link is a separate source equality.

No trivial action, inequality, PUnit/True, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaLinkCommonKummerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.KummerEvaluationArrowsActual2
open LeanFormal.IUT.XiFPaper.ThetaLinkKummerObjectsActualAdapted
open LeanFormal.IUT.XiFPaper.ThetaLinkProfiniteTopologyActualAdapted
open CategoryTheory

universe uG uv ua upi umon ui

variable {V : Type uv}

/-- The common abstract four-corner product group. -/
abbrev CommonG (S00 S01 S10 S11 : FPrimeStrip V) : Type _ :=
  FourCornerGroup S00 S01 S10 S11

/-- The actual profinite-completion topology on CommonG. -/
noncomputable instance commonGTopology (S00 S01 S10 S11 : FPrimeStrip V) :
    TopologicalSpace (CommonG S00 S01 S10 S11) :=
  TopologicalSpace.induced
    (profiniteCompletionEta
      (GrpCat.of (CommonG S00 S01 S10 S11))).hom
    inferInstance

/-- First projection from the common four-corner group to S00. -/
def commonFactorS00 (S00 S01 S10 S11 : FPrimeStrip V) (v : V) :
    CommonG S00 S01 S10 S11 →* S00.toDPrimeStrip.Pi v where
  toFun f := (f v).1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection from the common four-corner group to S01. -/
def commonFactorS01 (S00 S01 S10 S11 : FPrimeStrip V) (v : V) :
    CommonG S00 S01 S10 S11 →* S01.toDPrimeStrip.Pi v where
  toFun f := (f v).2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection from the common four-corner group to S10. -/
def commonFactorS10 (S00 S01 S10 S11 : FPrimeStrip V) (v : V) :
    CommonG S00 S01 S10 S11 →* S10.toDPrimeStrip.Pi v where
  toFun f := (f v).2.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection from the common four-corner group to S11. -/
def commonFactorS11 (S00 S01 S10 S11 : FPrimeStrip V) (v : V) :
    CommonG S00 S01 S10 S11 →* S11.toDPrimeStrip.Pi v where
  toFun f := (f v).2.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual lower action obtained from a strip equivalence and actual factor
maps. -/
noncomputable def factorLowerOfEquiv
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) (v : V) :
    G →* lower.toDPrimeStrip.Pi v :=
  (e.isoPi v).toMonoidHom.comp (factorUpper v)

/-- Equivariance of the x-mu quotient equivalence for arbitrary factor maps. -/
theorem xMuQuotientEquiv_equivariant_factors
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    (factorUpper : forall v : V, G →* upper.toDPrimeStrip.Pi v)
    (v : V) (g : G) (x : TimesMuQuotient ((upper.Mon v)ˣ)) :
    xMuQuotientEquiv upper lower e v
        (TimesMuQuotient.action
          ((upper.unitsAction v).comp (factorUpper v)) g x) =
      TimesMuQuotient.action
        ((lower.unitsAction v).comp
          (factorLowerOfEquiv G upper lower e factorUpper v)) g
        (xMuQuotientEquiv upper lower e v x) := by
  refine Quotient.inductionOn x ?_
  intro u
  rw [TimesMuQuotient.action_quotientMap, TimesMuQuotient.congr_quotientMap,
    TimesMuQuotient.congr_quotientMap, TimesMuQuotient.action_quotientMap]
  apply congrArg TimesMuQuotient.quotientMap
  apply Units.ext
  simp only [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val,
    factorLowerOfEquiv, MonoidHom.comp_apply]
  exact e.compatAction v (factorUpper v g) (u : upper.Mon v)

/-- The actual Kummer isomorphism from the actual strip equivalence and factor
maps. -/
noncomputable def kappaLowerOfFactors
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) (v : V) :
    TimesMuKummer.Isomorphism
      ((upper.unitsAction v).comp (factorUpper v))
      ((lower.unitsAction v).comp
        (factorLowerOfEquiv G upper lower e factorUpper v)) where
  equiv := xMuQuotientEquiv upper lower e v
  equivariant := by
    intro g x
    refine Quotient.inductionOn x ?_
    intro u
    rw [TimesMuQuotient.action_quotientMap, TimesMuQuotient.congr_quotientMap,
      TimesMuQuotient.congr_quotientMap, TimesMuQuotient.action_quotientMap]
    apply congrArg TimesMuQuotient.quotientMap
    apply Units.ext
    simp only [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val,
      factorLowerOfEquiv, MonoidHom.comp_apply]
    exact e.compatAction v (factorUpper v g) (u : upper.Mon v)
  invariantImage := by
    intro H
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (TimesMuKummer.mem_invariantImage_iff
        ((upper.unitsAction v).comp (factorUpper v)) H x).mp hx with
        ⟨u, hu, rfl⟩
      refine (TimesMuKummer.mem_invariantImage_iff
        ((lower.unitsAction v).comp
          (factorLowerOfEquiv G upper lower e factorUpper v)) H
        (xMuQuotientEquiv upper lower e v
          (TimesMuQuotient.quotientMap u))).mpr
        ⟨Units.mapEquiv (e.isoMon v) u, ?_, ?_⟩
      · intro g
        apply Units.ext
        simp only [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val,
          factorLowerOfEquiv, MonoidHom.comp_apply]
        rw [← e.compatAction v (factorUpper v g) (u : upper.Mon v)]
        exact congrArg (e.isoMon v) (hu g)
      · rw [TimesMuQuotient.congr_quotientMap]
    · intro hy
      obtain ⟨u, hu⟩ := TimesMuQuotient.quotientMap_surjective
        ((xMuQuotientEquiv upper lower e v).symm y)
      refine ⟨(xMuQuotientEquiv upper lower e v).symm y, ?_, ?_⟩
      · refine (TimesMuKummer.mem_invariantImage_iff
          ((upper.unitsAction v).comp (factorUpper v)) H
          ((xMuQuotientEquiv upper lower e v).symm y)).mpr
          ⟨u, ?_, hu⟩
        intro g
        apply (xMuQuotientEquiv upper lower e v).injective
        rw [xMuQuotientEquiv_equivariant_factors G upper lower e factorUpper v]
        · rw [MulEquiv.apply_symm_apply]
          exact TimesMuKummer.invariantImage_fixed
            ((lower.unitsAction v).comp
              (factorLowerOfEquiv G upper lower e factorUpper v)) H hy g
        · exact (xMuQuotientEquiv upper lower e v).apply_symm_apply y
      · exact (xMuQuotientEquiv upper lower e v).apply_symm_apply y

/-- Actual KappaOrbitUnitsActionPairDatum on an arbitrary topological group
with actual factor maps. -/
noncomputable def pairDatumOfFactors
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) :
    KappaOrbitUnitsActionPairDatum G upper lower where
  sourceUnits := fun v => (upper.Mon v)ˣ
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := fun v => (upper.unitsAction v).comp (factorUpper v)
  factorUpper := factorUpper
  factorLower := fun v => factorLowerOfEquiv G upper lower e factorUpper v
  kappaUpper := fun v =>
    TimesMuKummer.Isomorphism.refl
      ((upper.unitsAction v).comp (factorUpper v))
  kappaLower := fun v =>
    kappaLowerOfFactors G upper lower e factorUpper v

/-- The actual Kummer layer on an arbitrary topological group. -/
noncomputable def layerOfFactors
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) :
    SourceTimesMuKummerLayer G upper lower :=
  layerOfPair (pairDatumOfFactors G upper lower e factorUpper)

/-- The actual unit portion on an arbitrary topological group. -/
noncomputable def evalPortionOfFactors
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) (e : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) :
    SourceEvaluationUnitPortion G upper lower :=
  evalPortionOfPair (pairDatumOfFactors G upper lower e factorUpper)

/-! ## Actual four-corner arrows on CommonG -/

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev S00 : FPrimeStrip V := I.primeStripAt 0 0

abbrev S01 : FPrimeStrip V := I.primeStripAt 0 1

abbrev S10 : FPrimeStrip V := I.primeStripAt 1 0

abbrev S11 : FPrimeStrip V := I.primeStripAt 1 1

abbrev G4 : Type _ := CommonG (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))

noncomputable instance g4Topology : TopologicalSpace (G4 (I := I)) :=
  commonGTopology (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))

/-- Actual upper evaluation S00 -> S01. -/
noncomputable def actualUpperEvaluation : SourceEvaluationArrow (G4 (I := I))
    (S00 (I := I)) (S01 (I := I)) :=
  sourceEvaluationArrowOfUnitPortion
    ((I.linkAt 0 0 0 1).primeStripEquiv)
    (evalPortionOfFactors (G4 (I := I)) (S00 (I := I)) (S01 (I := I))
      ((I.linkAt 0 0 0 1).primeStripEquiv)
      (commonFactorS00 (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))))

/-- Actual left Kummer S10 -> S00. -/
noncomputable def actualLeftKummer : SourceKummerArrow (G4 (I := I))
    (S10 (I := I)) (S00 (I := I)) :=
  sourceKummerArrowOfLayer
    ((I.linkAt 1 0 0 0).primeStripEquiv)
    (layerOfFactors (G4 (I := I)) (S10 (I := I)) (S00 (I := I))
      ((I.linkAt 1 0 0 0).primeStripEquiv)
      (commonFactorS10 (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))))

/-- Actual right Kummer S11 -> S01. -/
noncomputable def actualRightKummer : SourceKummerArrow (G4 (I := I))
    (S11 (I := I)) (S01 (I := I)) :=
  sourceKummerArrowOfLayer
    ((I.linkAt 1 1 0 1).primeStripEquiv)
    (layerOfFactors (G4 (I := I)) (S11 (I := I)) (S01 (I := I))
      ((I.linkAt 1 1 0 1).primeStripEquiv)
      (commonFactorS11 (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))))

/-- Actual lower unit portion S10 -> S11. -/
noncomputable def actualLowerUnitPortion : SourceEvaluationUnitPortion
    (G4 (I := I)) (S10 (I := I)) (S11 (I := I)) :=
  evalPortionOfFactors (G4 (I := I)) (S10 (I := I)) (S11 (I := I))
    ((I.linkAt 1 0 1 1).primeStripEquiv)
    (commonFactorS10 (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I)))

/-- The actual four-corner Kummer-evaluation square. -/
noncomputable def actualKummerEvaluation : KummerEvaluationActual (G := G4 (I := I))
    (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I)) where
  square := SourceKummerEvaluationSquare.ofThreeLegs
    (actualUpperEvaluation (I := I))
    (actualLeftKummer (I := I))
    (actualRightKummer (I := I))
    (actualLowerUnitPortion (I := I))

/-- Actual Kummer arrow S00 -> S01 on the common group. -/
noncomputable def actualKummerS00S01 : SourceKummerArrow (G4 (I := I))
    (S00 (I := I)) (S01 (I := I)) :=
  sourceKummerArrowOfLayer
    ((I.linkAt 0 0 0 1).primeStripEquiv)
    (layerOfFactors (G4 (I := I)) (S00 (I := I)) (S01 (I := I))
      ((I.linkAt 0 0 0 1).primeStripEquiv)
      (commonFactorS00 (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))))

/-- Actual evaluation arrow S01 -> S11 on the common group. -/
noncomputable def actualEvaluationS01S11 : SourceEvaluationArrow (G4 (I := I))
    (S01 (I := I)) (S11 (I := I)) :=
  sourceEvaluationArrowOfUnitPortion
    ((I.linkAt 0 1 1 1).primeStripEquiv)
    (evalPortionOfFactors (G4 (I := I)) (S01 (I := I)) (S11 (I := I))
      ((I.linkAt 0 1 1 1).primeStripEquiv)
      (commonFactorS01 (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))))

/-- The actual IPL inequality-free factorization object: the actual paper link
S10 -> S11 equals the composite through S00 and S01. -/
noncomputable def actualIPL : IPLActual (G := G4 (I := I))
    (S10 (I := I)) (S10 (I := I)) (S00 (I := I)) (S01 (I := I)) (S11 (I := I)) where
  lowerHorizontal1 := FPrimeStripEquiv.refl (S10 (I := I))
  lowerHorizontal2 := (I.linkAt 1 0 0 0).primeStripEquiv.symm
  kummer := actualKummerS00S01 (I := I)
  evaluation := actualEvaluationS01S11 (I := I)
  inputLink := (I.linkAt 1 0 1 1).primeStripEquiv
  factorization := by
    have hlink : HodgeTheaterLink.trans
        (HodgeTheaterLink.trans (I.linkAt 1 0 0 0) (I.linkAt 0 0 0 1))
        (HodgeTheaterLink.symm (I.linkAt 1 1 0 1)) =
        I.linkAt 1 0 1 1 := by
      rw [I.linkAt_trans 1 0 0 0 0 1, I.linkAt_symm 1 1 0 1,
        I.linkAt_trans 1 0 0 1 0 1 1 1]
    have hprime := congrArg HodgeTheaterLink.primeStripEquiv hlink
    convert hprime using 2
    · simp [FPrimeStripEquiv.symm]
    · rw [FPrimeStripEquiv.trans_assoc]

/-- The constructed actual IPL factorization: inputLink equals composite. -/
theorem actualIPL_factorization :
    (actualIPL (I := I)).inputLink = (actualIPL (I := I)).composite :=
  (actualIPL (I := I)).inputLink_eq_composite

/-- The actual Kummer-evaluation square commutes. -/
theorem actualKummerEvaluation_commutes :
    (actualKummerEvaluation (I := I)).square.domainExpression =
      (actualKummerEvaluation (I := I)).square.codomainExpression :=
  (actualKummerEvaluation (I := I)).square.domainExpression_eq_codomainExpression

end LeanFormal.IUT.XiFPaper.ThetaLinkCommonKummerActualAdapted

end