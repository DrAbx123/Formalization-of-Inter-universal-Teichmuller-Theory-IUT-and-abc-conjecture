import tmp.sheaf.xif.paper.S1387D9PaperSlotActual
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# S1421: the actual D9 orbicurve X over K of paper type (1, l-tors)

S1376 restates the paper K-core C_K = C_F x_F K with the finite-etale cover
X_K -> C_K; S1319 constructs the actual sign quotient at the point level and
S1348 constructs the actual degree-two finite-etale cover of the Gaussian
punctured curve.  What was missing for the D9 first field was an actual
X : HyperbolicOrbicurve K of signature (1, l-tors) which is not the terminal
constant stack and not a point fiber.

This file constructs such an X from the actual S1348 finite-etale cover
scheme:

* the discrete stack of a type-valued etale sheaf is a stack for the big etale
  topology (discreteSheafFiber_isStack, proved for an arbitrary site; the key
  point is that the fibers are discrete, so descent data is governed by the
  sheaf condition, including the empty cover);
* the representable sheaf of the actual S1348 cover scheme
  Spec (R (x)_K (K x K)) is an etale sheaf, because the etale topology is
  subcanonical (it is coarser than the pro-etale topology);
* its discrete stack has a genuinely non-point fiber at the base scheme: the
  actual K-points of the cover, i.e. the elements of S1348Cover l, embed in
  the base sections, and S1348 proves that this type has two distinct
  elements (the two sheet lifts of an actual punctured point);
* inserting the paper (1, l-tors) signature gives the actual
  X : HyperbolicOrbicurve K, the exact first field of D9 (d9FirstField),
  together with its nonterminality, its non-point fiber, and the exclusion of
  the terminal constant stack and of the degenerate point-fiber orbicurve.

The D6 orbifold fundamental-group data (the OrbicurveFundamentalGroupData and
the exact sequence) is not constructed here; this file only supplies the exact
first field, as requested.  No terminal stack, point fiber, arbitrary carrier,
new axiom or sorry is used as a substitute.
-/


noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1421D9XActual

universe u v w

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped SpecOfNotation

/-! ## 1. The discrete stack of a type-valued sheaf -/

/-- The functor from the site to Cat whose value at U is the discrete
category on the type-valued sheaf X at U. -/
noncomputable def discreteCatFunctor {C : Type u} [Category.{v} C]
    (X : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Cat.{w,w} where
  obj U := Cat.of (Discrete (X.obj U))
  map {U V} f :=
    (Discrete.functor (fun i : X.obj U => Discrete.mk (X.map f i))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    simp
  map_comp {U V W} f g := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    simp

/-- The category-valued pseudofunctor with discrete fibers attached to a
type-valued presheaf. -/
noncomputable def discreteSheafFiber {C : Type u} [Category.{v} C]
    (X : Cᵒᵖ ⥤ Type w) :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w,w} :=
  (discreteCatFunctor X).toPseudofunctor'

namespace discreteSheafFiber

variable {C : Type u} [Category.{v} C]
variable {X : Cᵒᵖ ⥤ Type w} {J : GrothendieckTopology C}

/-- The sheaf condition at the empty sieve gives a subsingleton and an
inhabited value.  This is used for the empty-index case of the stack
condition. -/
lemma subsingleton_of_bot_mem (hX : Presieve.IsSheaf J X) {S : C}
    (h : (⊥ : Sieve S) ∈ J S) :
    Subsingleton (X.obj (op S)) ∧ Nonempty (X.obj (op S)) := by
  have hsheaf : Presieve.IsSheafFor X (⊥ : Presieve S) := hX (⊥ : Sieve S) h
  let x : (⊥ : Presieve S).FamilyOfElements X :=
    fun Y f hf => (show False from hf).elim
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    exact (show False from h₁).elim
  obtain ⟨t, ht, huniq⟩ := hsheaf x hx
  refine ⟨⟨fun a b => ?_⟩, ⟨t⟩⟩
  have ha : x.IsAmalgamation a := by
    intro Y f hf; exact (show False from hf).elim
  have hb : x.IsAmalgamation b := by
    intro Y f hf; exact (show False from hf).elim
  exact (huniq a ha).trans (huniq b hb).symm

end discreteSheafFiber

/-- The discrete stack of a type-valued sheaf is a stack for the topology:
all fibers are discrete, so descent data is exactly a compatible family of
sections of the sheaf. -/
theorem discreteSheafFiber_isStack {C : Type u} [Category.{v} C]
    (X : Cᵒᵖ ⥤ Type w) {J : GrothendieckTopology C}
    (hX : Presieve.IsSheaf J X) :
    (discreteSheafFiber X).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R hR
  rw [Pseudofunctor.isStackFor_iff]
  let f : (i : R.arrows.category) → i.obj.left ⟶ S := fun i => i.obj.hom
  haveI : ∀ (D₁ D₂ : (discreteSheafFiber X).DescentData f),
      Subsingleton (D₁ ⟶ D₂) := by
    intro D₁ D₂
    refine ⟨fun φ ψ => ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    let d₁ : Discrete (X.obj (op i.obj.left)) := D₁.obj i
    let d₂ : Discrete (X.obj (op i.obj.left)) := D₂.obj i
    exact Subsingleton.elim (α := d₁ ⟶ d₂) (φ.hom i) (ψ.hom i)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun {M N} φ ψ h => ?_⟩
    let m : Discrete (X.obj (op S)) := M
    let n : Discrete (X.obj (op S)) := N
    exact Subsingleton.elim (α := m ⟶ n) φ ψ
  · refine ⟨fun {M N} g => ?_⟩
    let M' : Discrete (X.obj (op S)) := M
    let N' : Discrete (X.obj (op S)) := N
    by_cases hι : Nonempty R.arrows.category
    · have hfam : ∀ {Y : C} (g₀ : Y ⟶ S) (hg₀ : R.arrows g₀),
          X.map g₀.op M'.as = X.map g₀.op N'.as := by
        intro Y g₀ hg₀
        let i : R.arrows.category := Presieve.categoryMk R.arrows g₀ hg₀
        let d₁ : Discrete (X.obj (op i.obj.left)) :=
          (((discreteSheafFiber X).toDescentData f).obj M).obj i
        let d₂ : Discrete (X.obj (op i.obj.left)) :=
          (((discreteSheafFiber X).toDescentData f).obj N).obj i
        have hcomp : d₁ ⟶ d₂ := g.hom i
        have heq : d₁.as = d₂.as := Discrete.eq_of_hom hcomp
        change d₁.as = d₂.as
        exact heq
      let fam : R.arrows.FamilyOfElements X :=
        fun Y g₀ hg₀ => X.map g₀.op M'.as
      have hcompFam : fam.Compatible := by
        intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
        simp only [fam]
        have h1 : X.map g₁.op (X.map f₁.op M'.as) =
            X.map (g₁ ≫ f₁).op M'.as := by
          rw [← comp_apply, ← Functor.map_comp, ← op_comp]
        have h2 : X.map (g₂ ≫ f₂).op M'.as =
            X.map g₂.op (X.map f₂.op M'.as) := by
          rw [op_comp, Functor.map_comp, comp_apply]
        calc
          X.map g₁.op (X.map f₁.op M'.as) = X.map (g₁ ≫ f₁).op M'.as := h1
          _ = X.map (g₂ ≫ f₂).op M'.as := by rw [comm]
          _ = X.map g₂.op (X.map f₂.op M'.as) := h2
      obtain ⟨t, ht, huniq⟩ := hX R hR fam hcompFam
      have hMt : fam.IsAmalgamation M'.as := by
        intro Y g₀ hg₀; rfl
      have hNt : fam.IsAmalgamation N'.as := by
        intro Y g₀ hg₀; exact (hfam g₀ hg₀).symm
      have hMN : M' = N' :=
        Discrete.ext ((huniq M'.as hMt).trans (huniq N'.as hNt).symm)
      refine ⟨Discrete.eqToHom (congrArg Discrete.as hMN), ?_⟩
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      let d₁ : Discrete (X.obj (op i.obj.left)) :=
        (((discreteSheafFiber X).toDescentData f).obj M).obj i
      let d₂ : Discrete (X.obj (op i.obj.left)) :=
        (((discreteSheafFiber X).toDescentData f).obj N).obj i
      exact Subsingleton.elim (α := d₁ ⟶ d₂)
        ((((discreteSheafFiber X).toDescentData f).map
          (Discrete.eqToHom (congrArg Discrete.as hMN))).hom i) (g.hom i)
    · haveI : IsEmpty R.arrows.category := ⟨fun i => hι ⟨i⟩⟩
      have hbot : (⊥ : Sieve S) ∈ J S := by
        have hRbot : R = ⊥ := by
          ext Y g₀
          constructor
          · intro hg₀
            exact isEmptyElim (Presieve.categoryMk R.arrows g₀ hg₀)
          · intro hg₀
            exact (show False from hg₀).elim
        rw [← hRbot]
        exact hR
      obtain ⟨hsub, hne⟩ :=
        discreteSheafFiber.subsingleton_of_bot_mem hX hbot
      haveI : Subsingleton (X.obj (op S)) := hsub
      let m : Discrete (X.obj (op S)) := M
      let n : Discrete (X.obj (op S)) := N
      have hMN : M = N := by
        change m = n
        exact Subsingleton.elim m n
      refine ⟨Discrete.eqToHom (congrArg Discrete.as hMN), ?_⟩
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      exact isEmptyElim i
  · refine ⟨fun D => ?_⟩
    let fam : R.arrows.FamilyOfElements X :=
      fun Y g₀ hg₀ => Discrete.as (D.obj (Presieve.categoryMk R.arrows g₀ hg₀))
    have hcomp : fam.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
      let i₁ : R.arrows.category := Presieve.categoryMk R.arrows f₁ h₁
      let i₂ : R.arrows.category := Presieve.categoryMk R.arrows f₂ h₂
      let d₁ : Discrete (X.obj (op Z)) :=
        ((discreteSheafFiber X).map g₁.op.toLoc).toFunctor.obj (D.obj i₁)
      let d₂ : Discrete (X.obj (op Z)) :=
        ((discreteSheafFiber X).map g₂.op.toLoc).toFunctor.obj (D.obj i₂)
      have hD : d₁ ⟶ d₂ :=
        D.hom (Y := Z) (q := g₁ ≫ f₁) (i₁ := i₁) (i₂ := i₂)
          g₁ g₂ rfl comm.symm
      have heq : d₁.as = d₂.as := Discrete.eq_of_hom hD
      change d₁.as = d₂.as
      exact heq
    obtain ⟨x, hx, huniq⟩ := hX R hR fam hcomp
    let xm : (discreteSheafFiber X).obj (LocallyDiscrete.mk (op S)) := Discrete.mk x
    let e : ∀ i, (((discreteSheafFiber X).toDescentData f).obj xm).obj i ≅ D.obj i :=
      fun i => Discrete.eqToIso (by
        let l : Discrete (X.obj (op i.obj.left)) :=
          (((discreteSheafFiber X).toDescentData f).obj xm).obj i
        let r : Discrete (X.obj (op i.obj.left)) := D.obj i
        change l.as = r.as
        exact hx i.obj.hom i.property)
    refine ⟨xm, ⟨Pseudofunctor.DescentData.isoMk e ?_⟩⟩
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    let d₁ : Discrete (X.obj (op Y)) :=
      ((discreteSheafFiber X).map f₁.op.toLoc).toFunctor.obj
        ((((discreteSheafFiber X).toDescentData f).obj xm).obj i₁)
    let d₂ : Discrete (X.obj (op Y)) :=
      ((discreteSheafFiber X).map f₂.op.toLoc).toFunctor.obj (D.obj i₂)
    change (show d₁ ⟶ d₂ from
        ((discreteSheafFiber X).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          D.hom q f₁ f₂ hf₁ hf₂) =
      (show d₁ ⟶ d₂ from
        (((discreteSheafFiber X).toDescentData f).obj xm).hom q f₁ f₂ hf₁ hf₂ ≫
          ((discreteSheafFiber X).map f₂.op.toLoc).toFunctor.map (e i₂).hom)
    exact Subsingleton.elim _ _

/-! ## 2. The actual S1348 cover scheme and its representable etale stack -/

namespace Paper

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1360D9OrbicurveSlotActual
open LeanFormal.IUT.XiFPaper.S1387D9PaperSlotActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

variable (l : PrimeGeFive)

/-- The K-side field over which the D9 orbicurve lives.  In the concrete
Gaussian input F = K, so this is definitionally the S1348 base field. -/
abbrev K : Type := (S1280Arithmetic l).K

/-- The actual S1348 finite-etale cover algebra
R (x)_K (K x K), where R = K[x,y]/(y^2 + xy - x^3 - 5) is the actual
affine coordinate ring of the Gaussian punctured curve. -/
abbrev CoverAlgebra : Type :=
  TensorProduct (S1348K l) (S1348CoordinateRing l) (S1348FiniteEtaleAlgebra l)

/-- The actual ring hom attached to an actual K-point of the cover. -/
noncomputable def coverRingHom (psi : S1348Cover l) :
    CoverAlgebra l →+* S1348K l :=
  { toFun := fun a => psi a
    map_one' := psi.map_one
    map_mul' := psi.map_mul
    map_zero' := psi.map_zero
    map_add' := psi.map_add }

/-- The corresponding morphism of affine schemes. -/
noncomputable def coverHom (psi : S1348Cover l) :
    CommRingCat.of (CoverAlgebra l) ⟶ CommRingCat.of (S1348K l) :=
  CommRingCat.ofHom (coverRingHom l psi)

/-- The actual S1348 finite-etale cover scheme over the Gaussian base. -/
noncomputable def coverScheme : Iut.SchemeOverField (S1348K l) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap (S1348K l) (CoverAlgebra l))))

/-- The base scheme Spec K over K. -/
noncomputable def base : Iut.SchemeOverField (S1348K l) :=
  baseSchemeObject (S1348K l)

/-- An actual K-point of the S1348 cover gives an actual section of the cover
scheme over the base. -/
noncomputable def sliceMap (psi : S1348Cover l) : base l ⟶ coverScheme l :=
  Over.homMk (Spec.map (coverHom l psi)) (by
    change Spec.map (coverHom l psi) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S1348K l) (CoverAlgebra l))) =
        𝟙 (Spec (CommRingCat.of (S1348K l)))
    rw [← Spec.map_comp]
    have hcomp : CommRingCat.ofHom (algebraMap (S1348K l) (CoverAlgebra l)) ≫
        coverHom l psi = 𝟙 (CommRingCat.of (S1348K l)) := by
      ext a
      exact psi.commutes a
    rw [hcomp, Spec.map_id])

/-- Distinct K-points of the cover give distinct sections of the cover
scheme: Spec is faithful on affine schemes. -/
theorem sliceMap_injective :
    Function.Injective (sliceMap l) := by
  intro psi1 psi2 h
  have hleft : Spec.map (coverHom l psi1) = Spec.map (coverHom l psi2) := by
    have h' := congrArg Over.Hom.left h
    change Spec.map (coverHom l psi1) = Spec.map (coverHom l psi2) at h'
    exact h'
  have hring := Spec.map_injective hleft
  apply AlgHom.ext
  intro a
  exact congrArg
    (fun f : CommRingCat.of (CoverAlgebra l) ⟶ CommRingCat.of (S1348K l) =>
      f.hom a) hring

local instance schemeEtaleSubcanonical :
    AlgebraicGeometry.Scheme.etaleTopology.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le
    AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology

local instance overEtaleSubcanonical :
    (Iut.SchemeOverField.etaleTopology (S1348K l)).Subcanonical :=
  GrothendieckTopology.subcanonical_over AlgebraicGeometry.Scheme.etaleTopology
    (Spec (CommRingCat.of (S1348K l)))

/-- The representable sheaf of the actual S1348 cover scheme is an etale
sheaf: the etale topology is subcanonical. -/
theorem coverSheaf :
    Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology (S1348K l))
      (yoneda.obj (coverScheme l)) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The actual non-point etale stack: the discrete stack of the representable
sheaf of the S1348 finite-etale cover scheme. -/
noncomputable def fiber : Iut.EtaleStackPseudofunctor (S1348K l) :=
  discreteSheafFiber (yoneda.obj (coverScheme l))

/-- The actual stack has effective descent for the big etale topology. -/
theorem fiber_isStack :
    (fiber l).IsStack (Iut.SchemeOverField.etaleTopology (S1348K l)) :=
  discreteSheafFiber_isStack _ (coverSheaf l)

/-- The actual sections of the cover scheme over the base are not a
subsingleton: the two distinct K-points of the S1348 cover give two distinct
sections. -/
theorem sections_not_subsingleton :
    ¬ Subsingleton (base l ⟶ coverScheme l) := by
  intro hsub
  apply S1348Cover_not_subsingleton l
  refine ⟨fun a b => ?_⟩
  exact sliceMap_injective l
    (hsub.allEq (sliceMap l a) (sliceMap l b))

/-- The actual fiber is not a point fiber. -/
theorem fiber_not_pointFiber : ¬ IsPointFiber (fiber l) := by
  intro h
  apply sections_not_subsingleton l
  have hd : Subsingleton (Discrete (base l ⟶ coverScheme l)) :=
    h (op (base l))
  exact ⟨fun a b => congrArg Discrete.as (hd.allEq (Discrete.mk a) (Discrete.mk b))⟩

/-- The fiber at the base scheme has two distinct objects, coming from the
two sheet lifts of an actual punctured point. -/
theorem fiber_base_nontrivial :
    ∃ x y : (fiber l).obj (LocallyDiscrete.mk (op (base l))), x ≠ y := by
  have hns : ¬ Subsingleton (S1348Cover l) := S1348Cover_not_subsingleton l
  push_neg at hns
  obtain ⟨a, b, hab⟩ := hns
  refine ⟨Discrete.mk (sliceMap l a), Discrete.mk (sliceMap l b), ?_⟩
  intro h
  exact hab (sliceMap_injective l (congrArg Discrete.as h))

/-- The actual D9 orbicurve: the paper (1, l-tors) signature inserted into the
actual non-point stack.  This is the exact first field of D9. -/
noncomputable def X : Iut.HyperbolicOrbicurve (K l) :=
  realizedHyperbolicOrbicurve (K l) (fiber l) (fiber_isStack l)
    (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l)

@[simp] theorem X_signature :
    (X l).signature = sourceTypeOneLTorsion l := rfl

/-- The exact first field is nonterminal. -/
theorem X_nonterminal : S1319NonterminalFiber (X l) := by
  rw [s1360Nonterminal_iff_not_pointFiber]
  show ¬ IsPointFiber (fiber l)
  exact fiber_not_pointFiber l

/-- The exact first field is not the terminal constant stack. -/
theorem X_not_terminal :
    (X l).stack ≠
      Definition31OrbicurveInstance.terminalConstantEtaleStack (K l) :=
  fun h =>
    Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
      (K l) (X l) h

/-- The exact first field is not the degenerate point-fiber orbicurve. -/
theorem X_ne_degeneratePointFiber :
    X l ≠ degeneratePointFiberOrbicurve (K l) := by
  intro h
  apply fiber_not_pointFiber l
  show IsPointFiber (X l).stack.fiber
  have hfiber : (X l).stack.fiber =
      (degeneratePointFiberOrbicurve (K l)).stack.fiber := by rw [h]
  rw [hfiber]
  exact degeneratePointFiberOrbicurve_isPointFiber (K l)

/-- The paper-typed first field of D9. -/
noncomputable def paperFirstField : S1360PaperOrbicurveFirstField l :=
  ⟨X l, X_signature l⟩

@[simp] theorem paperFirstField_val :
    (paperFirstField l : Iut.HyperbolicOrbicurve (K l)) = X l := rfl

/-- The exact first field of the S1387 D9 decomposition. -/
noncomputable def d9FirstField : S1387D9FirstField l :=
  { X := X l
    nonterminal := X_nonterminal l
    signature := X_signature l }

@[simp] theorem d9FirstField_X : (d9FirstField l).X = X l := rfl
@[simp] theorem d9FirstField_signature :
    (d9FirstField l).X.signature = sourceTypeOneLTorsion l :=
  (d9FirstField l).signature

/-- The stack content of the exact first field. -/
noncomputable def stackFirstField : S1387D9StackFirstField l :=
  { fiber := fiber l
    isStack := fiber_isStack l
    nonPoint := fiber_not_pointFiber l }

@[simp] theorem stackFirstField_fiber :
    (stackFirstField l).fiber = fiber l := rfl

/-- The S1387 constructor from an actual non-point fiber produces exactly the
D9 first field constructed here. -/
theorem d9FirstField_eq_ofFiber :
    d9FirstField l =
      S1387D9FirstFieldOfFiber l (fiber l) (fiber_isStack l)
        (fiber_not_pointFiber l) := rfl

/-- The base field of S1348 is definitionally the K-side field of S1280. -/
theorem baseField_eq_K : S1348K l = K l := rfl

end Paper

/-! ## 3. Axiom footprint -/

#print axioms discreteCatFunctor
#print axioms discreteSheafFiber
#print axioms discreteSheafFiber.subsingleton_of_bot_mem
#print axioms discreteSheafFiber_isStack
#print axioms Paper.coverRingHom
#print axioms Paper.coverHom
#print axioms Paper.coverScheme
#print axioms Paper.sliceMap
#print axioms Paper.sliceMap_injective
#print axioms Paper.coverSheaf
#print axioms Paper.fiber
#print axioms Paper.fiber_isStack
#print axioms Paper.sections_not_subsingleton
#print axioms Paper.fiber_not_pointFiber
#print axioms Paper.fiber_base_nontrivial
#print axioms Paper.X
#print axioms Paper.X_signature
#print axioms Paper.X_nonterminal
#print axioms Paper.X_not_terminal
#print axioms Paper.X_ne_degeneratePointFiber
#print axioms Paper.paperFirstField
#print axioms Paper.d9FirstField
#print axioms Paper.stackFirstField
#print axioms Paper.d9FirstField_eq_ofFiber

end LeanFormal.IUT.XiFPaper.S1421D9XActual
