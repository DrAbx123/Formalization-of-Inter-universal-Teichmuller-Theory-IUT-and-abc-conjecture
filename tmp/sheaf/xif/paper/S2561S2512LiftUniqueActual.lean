/-
# S2561: lift uniqueness for the concrete S2512 witness

The two-pullback witness `S2512Witness` of the representable base-change square is
the pointwise pullback lift of `S2512Lift`.  This file proves the lift-uniqueness
coherence `S2558LiftUnique` for that witness: any two 1-cells into the apex whose
composites with the two square legs are 2-isomorphic to the two legs of the same
cone are 2-isomorphic.

## The proof

For a cone `c` over the square and a 1-cell `phi` into the apex:

* a comparison 2-isomorphism `vcomp phi sq.toX ~ c.toX` gives, on every test
  object and every object of the source fibre, an equation
  `S2512Val phi U a ≫ S1742HomOfStrongTrans sq.toX = S2512Val c.toX U a`
  (`S2561Val_comp_toBase`), because 2-cells into a representable stack are
  subsingleton eliminations of discrete morphisms;
* after rewriting `sq.toX` and `sq.toY` by the identification with `pX` and `pY`,
  the two equations are the two projections of the map into the scheme pullback,
  so `IsPullback.hom_ext` proves pointwise equality with `S2512LiftVal`
  (`S2561ConeEssSurj`);
* two lifts are then 2-isomorphic by transitivity through the pointwise pullback
  lift, and the strong-transformation 2-isomorphism is assembled from pointwise
  equality by `S2512Val_isoOfValEq` (`S2561S2512LiftUnique`).

No sorry, no new axiom.  The theorem is the general-field form of the
"cone essential surjectivity" statement of S1911 (`S1911ConeEssSurj`), adapted to
the S2512 witness and stated in the `S2558LiftUnique` form used by the
extraction/EssSurj consumer chain.

## The concrete S2517 consumer

The general theorem is instantiated at the concrete finite-etale cover
`S2517InvObj C` of the S2482 orbicurve, whose base-change data are the S2512
pointwise pullback presentations of the scheme fibre product of the cover along
scheme-valued points.  This discharges `S2559HasLiftUnique` for that concrete
structure (`S2561S2517HasLiftUnique`).
-/
import tmp.sheaf.xif.paper.S2559ConcreteWitnessRefinementPlanActual
import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB
import tmp.sheaf.xif.paper.S2517InvObjActual

noncomputable section

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S2561S2512LiftUniqueActual

variable {F : Type} [Field F]

/-! ## 1. The two cone conditions, from a comparison 2-isomorphism -/

section Generic

variable {P X Y Z : Iut.SchemeOverField F} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : Iut.EtalePseudofunctorSquare (S2512YS P) (S2512YS X) (S2512YS Y) (S2512YS Z)}

/-- A comparison 2-isomorphism over the first leg gives the first cone condition
on values. -/
theorem S2561Val_comp_toBase
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S2512YS P))
    (e : Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX) :
    ∀ (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U),
      S2512Val phi U a ≫ S1742HomOfStrongTrans sq.toX = S2512Val c.toX U a := by
  intro U a
  have h := Discrete.eq_of_hom ((e.hom.as.app U).toNatTrans.app a)
  simpa only [← S2512Val_def, S2512Val_vcomp] using h

/-- A comparison 2-isomorphism over the second leg gives the second cone
condition on values. -/
theorem S2561Val_comp_toBaseY
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S2512YS P))
    (e : Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY) :
    ∀ (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U),
      S2512Val phi U a ≫ S1742HomOfStrongTrans sq.toY = S2512Val c.toY U a := by
  intro U a
  have h := Discrete.eq_of_hom ((e.hom.as.app U).toNatTrans.app a)
  simpa only [← S2512Val_def, S2512Val_vcomp] using h

/-- **Cone essential surjectivity of the concrete S2512 square.**  Any 1-cell
into the apex whose two projections are 2-isomorphic to the two legs of the cone
is 2-isomorphic to the pointwise pullback lift. -/
theorem S2561ConeEssSurj
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    (hX : sq.toX = S1742StrongTransOfHom pX)
    (hY : sq.toY = S1742StrongTransOfHom pY)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S2512YS P))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY) :
    Nonempty (Iso phi (S2512Lift hpb W c)) := by
  have hXc := S2561Val_comp_toBase c phi eX
  have hYc := S2561Val_comp_toBaseY c phi eY
  have hX' : S1742HomOfStrongTrans sq.toX = pX := by
    rw [hX, S1742HomOfStrongTrans_strongTransOfHom]
  have hY' : S1742HomOfStrongTrans sq.toY = pY := by
    rw [hY, S1742HomOfStrongTrans_strongTransOfHom]
  refine S2512Val_isoOfValEq (fun U a => ?_)
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2512Val phi U a) = Over.Hom.left (S2512LiftVal hpb c U a)
  apply IsPullback.hom_ext hpb
  · rw [S2512LiftVal_fst_left]
    rw [hX'] at hXc
    exact congrArg Over.Hom.left (hXc U a)
  · rw [S2512LiftVal_snd_left]
    rw [hY'] at hYc
    exact congrArg Over.Hom.left (hYc U a)

/-! ## 2. Lift uniqueness of the concrete S2512 witness -/

/-- **The lift-uniqueness coherence of the concrete S2512 witness.**  Two lifts
of the same cone (each equipped with comparison 2-isomorphisms to the two legs)
are 2-isomorphic.  This is `S2558LiftUnique` at `S2512Witness`; the witness
argument is unused by the statement, only the pointwise pullback lift is used. -/
theorem S2561S2512LiftUnique
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    (hX : sq.toX = S1742StrongTransOfHom pX)
    (hY : sq.toY = S1742StrongTransOfHom pY) :
    S2558LiftUnique sq (S2512Witness hpb hX hY) := by
  intro W c L1 L2 h1 h2
  obtain ⟨e1⟩ :=
    S2561ConeEssSurj hpb hX hY c L1 h1.toX h1.toY
  obtain ⟨e2⟩ :=
    S2561ConeEssSurj hpb hX hY c L2 h2.toX h2.toY
  exact ⟨e1 ≪≫ e2.symm⟩

end Generic

/-! ## 3. The concrete S2517 finite-etale structure -/

section S2517

open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517StackPresentationActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-- **Lift uniqueness for the concrete S2517 finite-etale cover.**  The
base-change data of `S2517InvObj C` are the concrete S2512 presentations: the
scheme pullback of the finite-etale cover `C` along the scheme-valued point
underlying `q`, with witness the pointwise pullback lift.  The general theorem
`S2561S2512LiftUnique` therefore discharges `S2559HasLiftUnique` for this
structure. -/
theorem S2561S2517HasLiftUnique (C : FiniteEtaleCover S2482AffineScheme) :
    S2559HasLiftUnique (S2517InvObj C).finiteEtale := by
  intro T q
  have hpb : IsPullback (S2517ToSource C T q).left
      (S2517Projection C T q).left
      (S2512BaseF (S2517Square C T q)).left
      (S2512BaseG (S2517Square C T q)).left := by
    rw [show S2512BaseF (S2517Square C T q) = S2517OverMap C from by
          change S1742HomOfStrongTrans (S2517Square C T q).xToBase = S2517OverMap C
          rw [show (S2517Square C T q).xToBase =
                S1742StrongTransOfHom (S2517OverMap C) from rfl,
            S1742HomOfStrongTrans_strongTransOfHom],
        show S2512BaseG (S2517Square C T q) = S2517G T q from rfl]
    exact IsPullback.of_hasPullback C.obj.hom (S2517G T q).left
  exact S2561S2512LiftUnique (pX := S2517ToSource C T q)
    (pY := S2517Projection C T q) hpb rfl rfl

end S2517

/-! ## 4. Target-locked statement checks and axiom audit -/

#check @S2561S2512LiftUnique
#check @S2561ConeEssSurj
#check @S2561S2517HasLiftUnique

#print axioms S2561Val_comp_toBase
#print axioms S2561Val_comp_toBaseY
#print axioms S2561ConeEssSurj
#print axioms S2561S2512LiftUnique
#print axioms S2561S2517HasLiftUnique

end LeanFormal.IUT.XiFPaper.S2561S2512LiftUniqueActual