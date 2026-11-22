import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace S1815Probe0

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} R)

abbrev shapePoint (G : Type u) : (SingleObj G)ᵒᵖ := Opposite.op (SingleObj.star G)

abbrev actionAlgebra (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} R) : Type u :=
  (F.obj (shapePoint G)).obj

noncomputable def opHom (g : G) : shapePoint G ⟶ shapePoint G :=
  (SingleObj.toEnd G g).op

lemma opHom_mul_inv (g : G) : opHom (G := G) g ≫ opHom (G := G) (g⁻¹) = 𝟙 _ := by
  unfold opHom
  change (SingleObj.toEnd G g * SingleObj.toEnd G (g⁻¹)).op = 𝟙 _
  rw [← map_mul, mul_inv_cancel]
  rfl

lemma opHom_inv_mul (g : G) : opHom (G := G) (g⁻¹) ≫ opHom (G := G) g = 𝟙 _ := by
  unfold opHom
  change (SingleObj.toEnd G (g⁻¹) * SingleObj.toEnd G g).op = 𝟙 _
  rw [← map_mul, inv_mul_cancel]
  rfl

noncomputable def sigma (g : G) : actionAlgebra F ≃ₐ[R] actionAlgebra F where
  toFun := (F.map (opHom (G := G) g)).hom.hom
  invFun := (F.map (opHom (G := G) (g⁻¹))).hom.hom
  left_inv := by
    intro a
    change (F.map (opHom (G := G) (g⁻¹))).hom.hom ((F.map (opHom (G := G) g)).hom.hom a) = a
    have hcomp : F.map (opHom (G := G) g) ≫ F.map (opHom (G := G) (g⁻¹)) = 𝟙 (F.obj (shapePoint G)) := by
      rw [← F.map_comp, opHom_mul_inv]
      exact F.map_id _
    have h := congrArg (fun (m : F.obj (shapePoint G) ⟶ F.obj (shapePoint G)) => m.hom.hom a) hcomp
    simpa using h
  right_inv := by
    intro a
    change (F.map (opHom (G := G) g)).hom.hom ((F.map (opHom (G := G) (g⁻¹))).hom.hom a) = a
    have hcomp : F.map (opHom (G := G) (g⁻¹)) ≫ F.map (opHom (G := G) g) = 𝟙 (F.obj (shapePoint G)) := by
      rw [← F.map_comp, opHom_inv_mul]
      exact F.map_id _
    have h := congrArg (fun (m : F.obj (shapePoint G) ⟶ F.obj (shapePoint G)) => m.hom.hom a) hcomp
    simpa using h
  map_add' := by intro a b; exact map_add _ a b
  map_mul' := by intro a b; exact map_mul _ a b
  commutes' := by intro r; exact AlgHom.commutes _ r

lemma sigma_apply (g : G) (a : actionAlgebra F) :
    sigma (F := F) g a = (F.map (opHom (G := G) g)).hom.hom a := rfl


lemma opHom_mul (g h : G) : opHom (G := G) (g * h) = opHom (G := G) g ≫ opHom (G := G) h := by
  unfold opHom
  rw [map_mul]
  rfl

lemma sigma_one : sigma (F := F) 1 = 1 := by
  ext a
  rw [sigma_apply]
  have h1 : opHom (G := G) 1 = 𝟙 (shapePoint G) := by
    simp [opHom]
  rw [h1, F.map_id]
  rfl

lemma sigma_mul (g h : G) :
    sigma (F := F) (g * h) = sigma (F := F) h * sigma (F := F) g := by
  ext a
  simp only [sigma_apply, AlgEquiv.mul_apply]
  rw [opHom_mul, F.map_comp]
  rfl

/-- The left action homomorphism (using inverse to turn the anti-hom into a hom). -/
noncomputable def actionEquiv (g : G) : actionAlgebra F ≃+* actionAlgebra F :=
  (sigma (F := F) (g⁻¹)).toRingEquiv

lemma actionEquiv_one : actionEquiv (F := F) 1 = 1 := by
  ext a
  simp [actionEquiv, sigma_one]

lemma actionEquiv_mul (g h : G) :
    actionEquiv (F := F) (g * h) = actionEquiv (F := F) g * actionEquiv (F := F) h := by
  ext a
  change sigma (F := F) ((g * h)⁻¹) a =
    sigma (F := F) (g⁻¹) (sigma (F := F) (h⁻¹) a)
  rw [mul_inv_rev, sigma_mul]
  rfl

/-- The monoid homomorphism encoding the action. -/
noncomputable def actionHom : G →* (actionAlgebra F ≃+* actionAlgebra F) where
  toFun := actionEquiv (F := F)
  map_one' := actionEquiv_one (F := F)
  map_mul' := actionEquiv_mul (F := F)

/-- The induced multiplicative semiring action. -/
@[reducible] noncomputable def actionMulSemiringAction :
    MulSemiringAction G (actionAlgebra F) :=
  letI : MulSemiringAction (actionAlgebra F ≃+* actionAlgebra F) (actionAlgebra F) :=
    inferInstance
  MulSemiringAction.compHom (M := actionAlgebra F ≃+* actionAlgebra F)
    (R := actionAlgebra F) (actionHom (F := F))

/-- The action is R-linear. -/
theorem actionSMulCommClass :
    letI := actionMulSemiringAction (F := F)
    SMulCommClass G R (actionAlgebra F) := by
  letI := actionMulSemiringAction (F := F)
  exact
    { smul_comm := fun g r a => by
        change actionEquiv (F := F) g (r • a) = r • actionEquiv (F := F) g a
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact (sigma (F := F) (g⁻¹)).commutes r }


lemma action_smul (g : G) (a : actionAlgebra F) :
    letI := actionMulSemiringAction (F := F)
    g • a = actionEquiv (F := F) g a := rfl

/-- The invariant subalgebra. -/
noncomputable def invariants : Subalgebra R (actionAlgebra F) :=
  letI := actionMulSemiringAction (F := F)
  letI := actionSMulCommClass (F := F)
  FixedPoints.subalgebra R (actionAlgebra F) G

/-- The fixed-point algebra is finite etale over any commutative base ring. -/
theorem invariants_finiteEtale :
    Algebra.Etale R ↥(invariants (F := F)) ∧ Module.Finite R ↥(invariants (F := F)) :=
  letI := actionMulSemiringAction (F := F)
  letI := actionSMulCommClass (F := F)
  FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
    (R := R) (A := actionAlgebra F) (G := G)

/-- The invariant subalgebra as an object of the finite etale category. -/
noncomputable def invariantsObject : CommAlgCat.FiniteEtale.{u} R :=
  let h := invariants_finiteEtale (F := F)
  letI : Algebra.Etale R ↥(invariants (F := F)) := h.1
  letI : Module.Finite R ↥(invariants (F := F)) := h.2
  CommAlgCat.FiniteEtale.of R ↥(invariants (F := F))

/-- The structure map from the invariants to the acted algebra. -/
noncomputable def invariantsMap (j : (SingleObj G)ᵒᵖ) :
    invariantsObject (F := F) ⟶ F.obj j :=
  { hom := CommAlgCat.ofHom
      (Subalgebra.val (invariants (F := F)) :
        ↥(invariants (F := F)) →ₐ[R] (F.obj j).obj) }

/-- Naturality of the invariants cone. -/
theorem invariantsMap_naturality {j j' : (SingleObj G)ᵒᵖ} (f : j ⟶ j') :
    invariantsMap (F := F) j' = invariantsMap (F := F) j ≫ F.map f := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  show (Subalgebra.val (invariants (F := F)) : ↥(invariants (F := F)) →ₐ[R] (F.obj j').obj) =
    ((F.map f).hom.hom).comp
      (Subalgebra.val (invariants (F := F)) : ↥(invariants (F := F)) →ₐ[R] (F.obj j).obj)
  apply AlgHom.ext
  intro x
  show (Subalgebra.val (invariants (F := F))) x =
    ((F.map f).hom.hom) ((Subalgebra.val (invariants (F := F))) x)
  have hf : f = opHom (G := G) (Opposite.unop f) := by
    change f = (SingleObj.toEnd G (Opposite.unop f)).op
    rw [SingleObj.toEnd_def]
    exact (Quiver.Hom.op_unop f).symm
  rw [hf]
  have hx : sigma (F := F) (Opposite.unop f)
      ((Subalgebra.val (invariants (F := F))) x) =
      (Subalgebra.val (invariants (F := F))) x := by
    have h := x.2 ((Opposite.unop f)⁻¹)
    simpa [action_smul, actionEquiv, inv_inv] using h
  exact hx.symm

/-- The invariants cone. -/
noncomputable def invariantsCone : Cone F where
  pt := invariantsObject (F := F)
  π :=
    { app := invariantsMap (F := F)
      naturality := by
        intro j j' f
        exact invariantsMap_naturality (F := F) f }

/-- The factorization of a cone through the invariants. -/
noncomputable def invariantsLift (c : Cone F) :
    c.pt ⟶ (invariantsCone (F := F)).pt :=
  { hom := CommAlgCat.ofHom
      (AlgHom.codRestrict ((c.π.app (shapePoint G)).hom.hom)
        (invariants (F := F)) (by
          intro x
          show ∀ g : G, actionEquiv (F := F) g
            ((c.π.app (shapePoint G)).hom.hom x) =
            (c.π.app (shapePoint G)).hom.hom x
          intro g
          change sigma (F := F) (g⁻¹) ((c.π.app (shapePoint G)).hom.hom x) =
            (c.π.app (shapePoint G)).hom.hom x
          exact congrArg
            (fun (m : c.pt ⟶ F.obj (shapePoint G)) => m.hom.hom x)
            (Cone.w (j := shapePoint G) (j' := shapePoint G) c (opHom (G := G) (g⁻¹))))) }

/-- The lift makes the triangles commute. -/
theorem invariantsLift_fac (c : Cone F) (j : (SingleObj G)ᵒᵖ) :
    invariantsLift (F := F) c ≫ (invariantsCone (F := F)).π.app j = c.π.app j := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

/-- The invariants cone is a limit cone. -/
noncomputable def invariantsIsLimit : IsLimit (invariantsCone (F := F)) where
  lift := invariantsLift (F := F)
  fac := invariantsLift_fac (F := F)
  uniq c m hm := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have h3 : m ≫ (invariantsCone (F := F)).π.app (shapePoint G) =
        invariantsLift (F := F) c ≫ (invariantsCone (F := F)).π.app (shapePoint G) := by
      rw [hm (shapePoint G), invariantsLift_fac (F := F) c (shapePoint G)]
    have h4 := congrArg (fun (g : c.pt ⟶ F.obj (shapePoint G)) => g.hom.hom x) h3
    exact Subtype.ext h4

instance hasLimitInvariants : HasLimit F :=
  HasLimit.mk ⟨invariantsCone (F := F), invariantsIsLimit (F := F)⟩

instance hasLimitsOfShapeOpSingleObj :
    HasLimitsOfShape (SingleObj G)ᵒᵖ (CommAlgCat.FiniteEtale.{u} R) :=
  ⟨fun F => hasLimitInvariants (F := F)⟩

/-- The opposite finite etale algebra category has finite-group quotient colimits. -/
instance hasColimitsOfShape_finiteEtaleAlg :
    HasColimitsOfShape (SingleObj G) ((CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :=
  hasColimitsOfShape_op_of_hasLimitsOfShape (J := SingleObj G)
    (C := CommAlgCat.FiniteEtale.{u} R)

end S1815Probe0