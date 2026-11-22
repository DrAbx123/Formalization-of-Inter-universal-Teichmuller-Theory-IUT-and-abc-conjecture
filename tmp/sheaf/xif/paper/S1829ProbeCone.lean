import tmp.sheaf.xif.paper.S1829FiberCoveredYonedaActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option pp.proofs false
set_option pp.universes false

namespace LeanFormal.IUT.XiFPaper.S1829ProbeCone

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1829FiberCoveredYonedaActual
open LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual.Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

variable (cover : S1735Cover)

abbrev W : EtaleStackPseudofunctor S1735K :=
  schemeRepresentableEtalePseudofunctor S1735K S1735BaseScheme

abbrev B := S1780BaseChange cover

variable (x : S1735Fiber cover)

/-- The underlying object of the geometric fibre object. -/
noncomputable abbrev YOf (x : S1735Fiber cover) : (cover.source.fiber).obj S1780Site :=
  x.left

/-- The comparison morphism of the geometric fibre object. -/
noncomputable abbrev fOf (x : S1735Fiber cover) :
    (cover.map.app S1780Site).toFunctor.obj (YOf cover x) ⟶ S1780PointObject :=
  x.hom

/-- The inverse Yoneda transformation attached to a geometric-fibre object. -/
noncomputable def sigmaOf (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans W cover.source.fiber :=
  ofObjY (G := cover.source.fiber) (YOf cover x)

/-- The first transformation to the representable target. -/
noncomputable def eta1 (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans W S1735Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.vcomp (sigmaOf cover x) cover.map

/-- The second transformation to the representable target. -/
noncomputable def eta2 (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans W S1735Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id W) S1735BasePoint

theorem hhom_eq (x : S1735Fiber cover) :
    S1742HomOfStrongTrans (eta1 cover x) = S1742HomOfStrongTrans (eta2 cover x) := by
  dsimp [eta1, eta2, sigmaOf, S1742HomOfStrongTrans, YOf]
  have hmor : (cover.map.app S1780Site).toFunctor.obj
        ((cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left)) =
      S1780PointObject := by
    let mId : (cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left) ⟶
        x.left :=
      (cover.source.fiber.mapId S1780Site).hom.toNatTrans.app (x.left)
    let m : (cover.map.app S1780Site).toFunctor.obj
          ((cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left)) ⟶
        S1780PointObject :=
      (cover.map.app S1780Site).toFunctor.map mId ≫ x.hom
    haveI : IsDiscrete ((S1735Orbicurve.stack.fiber).obj S1780Site) := by
      change IsDiscrete (Discrete (S1735BaseScheme ⟶ S1726AffineOver))
      infer_instance
    exact IsDiscrete.eq_of_hom m
  change ((cover.map.app S1780Site).toFunctor.obj
        ((cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left))).as =
      S1780PointObject.as
  exact congrArg (fun Z => Z.as) hmor

/-- The square of the actual point base change. -/
noncomputable abbrev square : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1735K (S1780Model cover))
    cover.source.fiber
    (schemeRepresentableEtalePseudofunctor S1735K S1735BaseScheme)
    S1735Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (S1780BaseChange cover).toSource
    (S1780BaseChange cover).projectionMap.transformation cover.map S1735BasePoint
    (S1780BaseChange cover).commutes

/-- The 2-isomorphism comparing the two legs of the would-be cone. -/
noncomputable def coneCommutes (x : S1735Fiber cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (sigmaOf cover x) cover.map)
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id W) S1735BasePoint) :=
  (S1742StrongTransIsoOfHom (eta1 cover x)).symm ≪≫
    eqToIso (congrArg S1742StrongTransOfHom (hhom_eq cover x)) ≪≫
      S1742StrongTransIsoOfHom (eta2 cover x)

/-- The cone from the represented base to the actual point base-change square. -/
noncomputable def testCone (x : S1735Fiber cover) : EtalePseudofunctorSquare.Cone (square cover) W :=
  { toX := sigmaOf cover x
    toY := Pseudofunctor.StrongTrans.id W
    commutes := coneCommutes cover x }

/-- The lift of the cone through the two-pullback universal property. -/
noncomputable def testLift (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans W (schemeRepresentableEtalePseudofunctor S1735K (S1780Model cover)) :=
  (S1780BaseChange cover).isPullback.lift W (testCone cover x)

/-- The section attached to a geometric-fibre object. -/
noncomputable def testSection (x : S1735Fiber cover) : S1735BaseScheme ⟶ S1780Model cover :=
  S1742HomOfStrongTrans (testLift cover x)

example (x : S1735Fiber cover) :
    ((testLift cover x).app S1780Site).toFunctor.obj (Discrete.mk (𝟙 S1735BaseScheme)) =
      Discrete.mk (testSection cover x) := by
  apply Discrete.ext
  rw [S1742Key (testLift cover x) S1780Site (𝟙 S1735BaseScheme)]
  exact Category.id_comp _

/-- A costructured-arrow category into a discrete target over a discrete source is
discrete. -/
instance isDiscreteCostructuredArrow {C D : Type*} [Category C] [Category D]
    [IsDiscrete C] [IsDiscrete D] (F : C ⥤ D) (T : D) :
    IsDiscrete (CostructuredArrow F T) where
  subsingleton X Y := ⟨fun f g => by
    apply CostructuredArrow.hom_ext
    exact Subsingleton.elim _ _⟩
  eq_of_hom {X Y} f := by
    cases X with
    | mk xl xr xh =>
    cases Y with
    | mk yl yr yh =>
    have h : xl = yl := IsDiscrete.eq_of_hom f.left
    subst h
    have hr : xr = yr := Subsingleton.elim _ _
    have hh : xh = yh := Subsingleton.elim _ _
    subst hr
    subst hh
    rfl

/-- The comparison morphism from the section-object to the given geometric-fibre
object, under discreteness of the source value. -/
noncomputable def testMorphism (x : S1735Fiber cover) :
    ((S1780BaseChange cover).toSource.app S1780Site).toFunctor.obj
        (Discrete.mk (testSection cover x)) ⟶ x.left := by
  let e := (S1780BaseChange cover).isPullback.liftToX W (testCone cover x)
  let m1 : ((Pseudofunctor.StrongTrans.vcomp (testLift cover x)
        (S1780BaseChange cover).toSource).app S1780Site).toFunctor.obj
        (Discrete.mk (𝟙 S1735BaseScheme)) ⟶
      ((sigmaOf cover x).app S1780Site).toFunctor.obj
        (Discrete.mk (𝟙 S1735BaseScheme)) :=
    (e.hom.as.app S1780Site).toNatTrans.app (Discrete.mk (𝟙 S1735BaseScheme))
  let m2 : ((sigmaOf cover x).app S1780Site).toFunctor.obj
        (Discrete.mk (𝟙 S1735BaseScheme)) ⟶ x.left :=
    (cover.source.fiber.mapId S1780Site).hom.toNatTrans.app (x.left)
  exact m1 ≫ m2

/-- Under discreteness of the source value, the section attached to a
geometric-fibre object strictly recovers its underlying stack object. -/
theorem testSection_source_eq (x : S1735Fiber cover)
    [IsDiscrete ((cover.source.fiber).obj S1780Site)] :
    ((S1780BaseChange cover).toSource.app S1780Site).toFunctor.obj
        (Discrete.mk (testSection cover x)) = x.left :=
  IsDiscrete.eq_of_hom (testMorphism cover x)

/-- **The second S1780 gap closes under discreteness of the source value.** -/
theorem fiberCovered_of_isDiscrete (cover : S1735Cover)
    [IsDiscrete ((cover.source.fiber).obj S1780Site)] :
    Function.Surjective (S1780SectionToFiber cover) := by
  intro x
  refine ⟨testSection cover x, ?_⟩
  haveI : IsDiscrete ((S1735Orbicurve.stack.fiber).obj S1780Site) := by
    change IsDiscrete (Discrete (S1735BaseScheme ⟶ S1726AffineOver))
    infer_instance
  haveI : IsDiscrete (S1735Fiber cover) :=
    isDiscreteCostructuredArrow (cover.map.app S1780Site).toFunctor S1780PointObject
  apply IsDiscrete.eq_of_hom
  refine CostructuredArrow.homMk (testMorphism cover x) ?_
  exact Subsingleton.elim _ _

/-- Every geometric-fibre object receives a morphism from a section image,
unconditionally: this is the essential-surjectivity half that the two-pullback
universal property supplies. -/
theorem section_covers_morphism (x : S1735Fiber cover) :
    ∃ s : S1735BaseScheme ⟶ S1780Model cover,
      Nonempty (S1780SectionToFiber cover s ⟶ x) := by
  haveI : IsDiscrete ((S1735Orbicurve.stack.fiber).obj S1780Site) := by
    change IsDiscrete (Discrete (S1735BaseScheme ⟶ S1726AffineOver))
    infer_instance
  exact ⟨testSection cover x, ⟨CostructuredArrow.homMk (testMorphism cover x)
    (Subsingleton.elim _ _)⟩⟩

/-- The exact remaining discreteness input, isolated. -/
def S1829FiberDiscrete : Prop :=
  ∀ cover : S1735Cover, IsDiscrete ((cover.source.fiber).obj S1780Site)

/-- Under `S1829FiberDiscrete`, every S1780 cover has every geometric-fibre
object in the strict image of the section map. -/
theorem S1780FiberCovered_of_fiberDiscrete (h : S1829FiberDiscrete)
    (cover : S1735Cover) : S1780FiberCovered cover :=
  @fiberCovered_of_isDiscrete cover (h cover)

/-- Under `S1829FiberDiscrete`, the packaged S1780 first missing input holds,
with the section-finiteness half supplied unconditionally by S1803. -/
theorem S1780FirstMissing_of_fiberDiscrete (h : S1829FiberDiscrete) :
    S1780FirstMissing :=
  ⟨fun cover => LeanFormal.IUT.XiFPaper.S1803AffineSectionsActual.S1803_sectionFintype cover,
    fun cover => S1780FiberCovered_of_fiberDiscrete h cover⟩

/-- Under `S1829FiberDiscrete`, the S1735 finiteness requirement follows. -/
theorem S1735GeometricFiberFintypeRequired_of_fiberDiscrete
    (h : S1829FiberDiscrete) : S1735GeometricFiberFintypeRequired :=
  S1780FintypeRequired_of_firstMissing (S1780FirstMissing_of_fiberDiscrete h)

end LeanFormal.IUT.XiFPaper.S1829ProbeCone