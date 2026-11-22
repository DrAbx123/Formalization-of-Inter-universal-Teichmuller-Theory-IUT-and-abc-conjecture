import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.SingleObj

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open scoped TensorProduct

namespace S1806G2

variable {R : Type} [CommRing R]

abbrev FiniteEtaleAlg : Type 1 := (CommAlgCat.FiniteEtale.{0} R)ᵒᵖ

section Action

variable {G : Type} [Group G]

abbrev actionAlgebra (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) : Type :=
  (F.obj (Opposite.op (SingleObj.star G))).obj

def actionMap (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) (g : G) :
    actionAlgebra F →ₐ[R] actionAlgebra F :=
  (F.map (Opposite.op g)).hom.hom

lemma actionMap_one (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) :
    actionMap F (1 : G) = AlgHom.id R (actionAlgebra F) := by
  unfold actionMap
  rw [show (Opposite.op (1 : G)) = 𝟙 (Opposite.op (SingleObj.star G)) from rfl, F.map_id]
  rfl

lemma actionMap_mul (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) (g h : G) :
    actionMap F (g * h) = (actionMap F h).comp (actionMap F g) := by
  unfold actionMap
  change (F.map (Opposite.op (g * h))).hom.hom =
    (F.map (Opposite.op g) ≫ F.map (Opposite.op h)).hom.hom
  rw [← F.map_comp]
  congr 1

noncomputable instance actionMulSemiringAction
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) :
    MulSemiringAction G (actionAlgebra F) where
  smul g x := actionMap F g⁻¹ x
  one_smul x := by
    change actionMap F ((1 : G)⁻¹) x = x
    rw [inv_one, actionMap_one]
    rfl
  mul_smul g h x := by
    change actionMap F ((g * h)⁻¹) x = actionMap F g⁻¹ (actionMap F h⁻¹ x)
    rw [mul_inv_rev, actionMap_mul]
    rfl
  smul_zero g := (actionMap F g⁻¹).map_zero
  smul_add g x y := (actionMap F g⁻¹).map_add x y
  smul_one g := (actionMap F g⁻¹).map_one
  smul_mul g x y := (actionMap F g⁻¹).map_mul x y

lemma action_smul_def (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) (g : G)
    (x : actionAlgebra F) : g • x = actionMap F g⁻¹ x := rfl

noncomputable instance actionSMulCommClass
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) :
    SMulCommClass G R (actionAlgebra F) where
  smul_comm g r x := by
    change actionMap F g⁻¹ (r • x) = r • actionMap F g⁻¹ x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, (actionMap F g⁻¹).commutes]

abbrev invariants (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) :
    Subalgebra R (actionAlgebra F) :=
  fixedPointSubalgebra R (actionAlgebra F) G

lemma groupActionRingEquiv_apply
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) (g : G) (x : actionAlgebra F) :
    groupActionRingEquiv (actionAlgebra F) G g x = actionMap F g⁻¹ x := by
  rfl

theorem invariants_finiteEtale [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) :
    Algebra.Etale R ↥(invariants F) ∧ Module.Finite R ↥(invariants F) := by
  haveI : Algebra.Etale R (actionAlgebra F) :=
    (F.obj (Opposite.op (SingleObj.star G))).property.right
  haveI : Module.Finite R (actionAlgebra F) :=
    (F.obj (Opposite.op (SingleObj.star G))).property.left
  exact FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
    (R := R) (A := actionAlgebra F) (G := G)

noncomputable def invariantsObject [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) :
    CommAlgCat.FiniteEtale.{0} R := by
  have h := invariants_finiteEtale (R := R) F
  letI : Algebra.Etale R ↥(invariants F) := h.1
  letI : Module.Finite R ↥(invariants F) := h.2
  exact CommAlgCat.FiniteEtale.of R ↥(invariants F)

noncomputable def invariantsMap [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R)
    (j : (SingleObj G)ᵒᵖ) : invariantsObject (R := R) F ⟶ F.obj j := by
  have h := invariants_finiteEtale (R := R) F
  letI : Algebra.Etale R ↥(invariants F) := h.1
  letI : Module.Finite R ↥(invariants F) := h.2
  exact CommAlgCat.FiniteEtale.ofHom (fixedPointInclusion R (actionAlgebra F) G)

lemma fixed_inclusion_action [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) (g : G)
    (x : ↥(invariants F)) :
    actionMap F g (x : actionAlgebra F) = (x : actionAlgebra F) := by
  have hfix : actionMap F g⁻¹ (x : actionAlgebra F) = (x : actionAlgebra F) := by
    have h := x.2 g
    simpa [action_smul_def] using h
  have hcomp : actionMap F g (actionMap F g⁻¹ (x : actionAlgebra F)) =
      actionMap F (g⁻¹ * g) (x : actionAlgebra F) := by
    rw [actionMap_mul]
    rfl
  calc actionMap F g (x : actionAlgebra F)
      = actionMap F g (actionMap F g⁻¹ (x : actionAlgebra F)) := by rw [hfix]
    _ = actionMap F (g⁻¹ * g) (x : actionAlgebra F) := hcomp
    _ = (x : actionAlgebra F) := by
        rw [inv_mul_cancel]
        exact congrArg (fun f => f (x : actionAlgebra F)) (actionMap_one F)

lemma invariantsMap_naturality [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R)
    {j j' : (SingleObj G)ᵒᵖ} (f : j ⟶ j') :
    invariantsMap F j' = invariantsMap F j ≫ F.map f := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  have hf : f = Opposite.op (Opposite.unop f) := (Opposite.op_unop f).symm
  rw [hf]
  exact (fixed_inclusion_action F (Opposite.unop f) x).symm

noncomputable def invariantsCone [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) : Cone F where
  pt := invariantsObject (R := R) F
  π :=
    { app := invariantsMap F
      naturality := by
        intro j j' f
        exact invariantsMap_naturality F f }

noncomputable def invariantsLiftAlgHom [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R)
    (c : Cone F) : (c.pt).obj →ₐ[R] ↥(invariants F) :=
  AlgHom.codRestrict
    ((c.π.app (Opposite.op (SingleObj.star G))).hom.hom) (invariants F)
    (fun b => by
      intro g
      have hnat := Cone.w (F := F) (j := Opposite.op (SingleObj.star G))
        (j' := Opposite.op (SingleObj.star G)) c (Opposite.op g⁻¹)
      have hb := congrArg
        (fun (m : c.pt ⟶ F.obj (Opposite.op (SingleObj.star G))) => m.hom.hom b) hnat
      rw [ObjectProperty.FullSubcategory.comp_hom, CommAlgCat.hom_comp, AlgHom.comp_apply] at hb
      change actionMap F g⁻¹ ((c.π.app (Opposite.op (SingleObj.star G))).hom.hom b) =
        (c.π.app (Opposite.op (SingleObj.star G))).hom.hom b
      exact hb)

noncomputable def invariantsLift [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R)
    (c : Cone F) : c.pt ⟶ (invariantsCone (R := R) F).pt := by
  have h := invariants_finiteEtale (R := R) F
  letI : Algebra.Etale R ↥(invariants F) := h.1
  letI : Module.Finite R ↥(invariants F) := h.2
  exact ObjectProperty.homMk (CommAlgCat.ofHom (invariantsLiftAlgHom F c))

lemma invariantsLift_fac [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R)
    (c : Cone F) (j : (SingleObj G)ᵒᵖ) :
    invariantsLift F c ≫ (invariantsCone (R := R) F).π.app j = c.π.app j := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

noncomputable def invariantsIsLimit [Fintype G] [DecidableEq G]
    (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} R) :
    IsLimit (invariantsCone (R := R) F) where
  lift := invariantsLift F
  fac := invariantsLift_fac F
  uniq c m hm := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    apply Subtype.ext
    have hb := congrArg
      (fun (q : c.pt ⟶ F.obj (Opposite.op (SingleObj.star G))) => q.hom.hom b)
      (hm (Opposite.op (SingleObj.star G)))
    exact hb

instance hasLimitsOfShape_op_singleObj [Finite G] :
    HasLimitsOfShape (SingleObj G)ᵒᵖ (CommAlgCat.FiniteEtale.{0} R) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  exact ⟨fun F => ⟨invariantsCone (R := R) F, invariantsIsLimit F⟩⟩

end Action

variable {G : Type} [Group G] [Finite G]

instance hasQuotientsByFiniteGroups :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg (R := R)) :=
  hasColimitsOfShape_op_of_hasLimitsOfShape (J := SingleObj G)
    (C := CommAlgCat.FiniteEtale.{0} R)

end S1806G2