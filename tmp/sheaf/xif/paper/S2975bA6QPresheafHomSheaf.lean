
/-
S2975b: the hom presheaf of the A6 pointwise pseudofunctor `S2882A6Q`.

New file; it does not modify S2882/S2893/S2899/S2903/S2975/S2976.

## Contents

* `pt`, `HomForm`: explicit model of the value of `Q.presheafHom M N` at a test object
  `T` with `p = T.unop.hom`: the subtype `{g : SignGroup // (p ≫ M) ≫ aut g = p ≫ N}`.
* `presheafHom_obj_eq`: the objectwise description of the hom presheaf.
* `subsingleton_of_bot_mem`: if the empty sieve covers `T`, the sheaf condition forces the
  value at `T` to be a subsingleton.
* `not_isSheaf_empty`, `S2975b_not_isPrestack`: on the empty base scheme the empty sieve is
  covering (`Scheme.bot_mem_grothendieckTopology`) and the value of `Q.presheafHom M M` there
  is the full sign group, so the sheaf condition fails.  Hence the literal A1 target
  `S2882A6Q.IsPrestack (etaleTopology K)` is false.
-/
import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
open CategoryTheory Opposite
open CategoryTheory.Limits
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2975bA6QPresheafHomSheaf

open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

abbrev K : Type := S2844D6F6BaseChangeActual.K
local instance : Field K := S2847A6.fieldF
local instance : NumberField K := S2847A6.numberFieldF
local instance : DecidableEq K := Classical.decEq _

/-- The represented curve. -/
abbrev X : Iut.SchemeOverField K := S2844D6F6BaseChangeActual.S2844X

/-- The etale topology on schemes over `Spec K`. -/
abbrev J : GrothendieckTopology (Iut.SchemeOverField K) := Iut.SchemeOverField.etaleTopology K

/-- The A6 pointwise pseudofunctor. -/
abbrev Q : Iut.EtaleStackPseudofunctor K := S2882A6Q

/-- The sign action on points of the curve, in the `S`-presentation. -/
local instance pointSMul (S : Iut.SchemeOverField K) : SMul SignGroup (S ⟶ X) :=
  S2882A6PointSMul (LocallyDiscrete.mk (Opposite.op S))

local instance pointMulAction (S : Iut.SchemeOverField K) : MulAction SignGroup (S ⟶ X) :=
  S2882A6PointMulAction (LocallyDiscrete.mk (Opposite.op S))

/-! ## 1. The objectwise description -/

section Objectwise

variable {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}

/-- The underlying point of an object of the fiber of `Q` at `U`. -/
def pt (M : Q.obj U) : Opposite.unop U.as ⟶ X := M.back

/-- Explicit model of the value of the hom presheaf at a test object `T`. -/
abbrev HomForm (M N : Q.obj U) (T : (Over (Opposite.unop U.as))ᵒᵖ) : Type :=
  { g : SignGroup // (T.unop.hom ≫ pt M) ≫ S2882A6Aut g = T.unop.hom ≫ pt N }

lemma map_obj_back {M : Q.obj U} (T : (Over (Opposite.unop U.as))ᵒᵖ) :
    ((Q.map T.unop.hom.op.toLoc).toFunctor.obj M).back = T.unop.hom ≫ M.back := rfl

/-- **Objectwise description of the hom presheaf.** -/
lemma presheafHom_obj_eq (M N : Q.obj U) (T : (Over (Opposite.unop U.as))ᵒᵖ) :
    (Q.presheafHom M N).obj T = HomForm M N T := rfl

end Objectwise

/-! ## 2. The sign action in the `S`-presentation -/

section Shift

variable (S : Iut.SchemeOverField K)

/-- The value of the hom presheaf at `T : (Over S)ᵒᵖ`, as an explicit subtype. -/
abbrev HomFormS (M N : Q.obj (LocallyDiscrete.mk (Opposite.op S))) (T : (Over S)ᵒᵖ) : Type :=
  { g : SignGroup // (T.unop.hom ≫ pt M) ≫ S2882A6Aut g = T.unop.hom ≫ pt N }

lemma presheafHom_obj_eqS (M N : Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    (Q.presheafHom M N).obj T = HomFormS S M N T :=
  presheafHom_obj_eq (U := LocallyDiscrete.mk (Opposite.op S)) M N T

end Shift

/-! ## 3. The empty-sieve obstruction -/

section Obstruction

variable {S : Iut.SchemeOverField K}

/-- If the empty sieve covers `T`, the sheaf condition forces the value of the hom presheaf
at `T` to be a subsingleton. -/
theorem subsingleton_of_bot_mem
    (M N : Q.obj (LocallyDiscrete.mk (Opposite.op S))) {T : Over S}
    (hT : (⊥ : Sieve T) ∈ J.over S T)
    (h : Presheaf.IsSheaf (J.over S) (Q.presheafHom M N)) :
    Subsingleton ((Q.presheafHom M N).obj (op T)) := by
  have h' : Presieve.IsSheaf (J.over S) (Q.presheafHom M N) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp h
  have hfor : Presieve.IsSheafFor (Q.presheafHom M N) ((⊥ : Sieve T) : Presieve T) :=
    h' (⊥ : Sieve T) hT
  let x : Presieve.FamilyOfElements (Q.presheafHom M N) ((⊥ : Sieve T) : Presieve T) :=
    fun Y f hf => hf.elim
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomp
    exact h₁.elim
  obtain ⟨t, -, huniq⟩ := hfor x hx
  exact ⟨fun a b => by
    rw [huniq a (fun Y f hf => hf.elim), huniq b (fun Y f hf => hf.elim)]⟩

end Obstruction

/-! ## 4. The empty base scheme and the refutation of A1 -/

section EmptyBase

/-- The empty scheme, as an object of the site over `Spec K`. -/
noncomputable def emptyBase : Iut.SchemeOverField K :=
  Over.mk (AlgebraicGeometry.Scheme.emptyTo
    (AlgebraicGeometry.Spec (CommRingCat.of K)))

instance : IsEmpty ↑emptyBase.left := by
  change IsEmpty (↥(∅ : AlgebraicGeometry.Scheme))
  infer_instance

/-- The unique point of the fiber of `Q` at the empty base. -/
noncomputable def emptyPt : emptyBase ⟶ X :=
  Over.homMk (AlgebraicGeometry.Scheme.emptyTo X.left)
    (AlgebraicGeometry.Scheme.empty_ext _ _)

/-- The object of the fiber of `Q` at the empty base. -/
noncomputable def emptyObj : Q.obj (LocallyDiscrete.mk (Opposite.op emptyBase)) :=
  (emptyPt : ActionCategory SignGroup (emptyBase ⟶ X))

lemma subsingleton_over_hom {S : Iut.SchemeOverField K} (hS : IsEmpty ↑S.left)
    (Y : Iut.SchemeOverField K) : Subsingleton (S ⟶ Y) := by
  haveI : IsEmpty ↑S.left := hS
  haveI hI : IsInitial S.left := AlgebraicGeometry.isInitialOfIsEmpty
  refine ⟨fun a b => ?_⟩
  have hleft : a.left = b.left := IsInitial.hom_ext hI a.left b.left
  exact CategoryTheory.CostructuredArrow.hom_ext a b hleft

/-- The empty sieve is covering at the empty base (test object `Over.mk (𝟙 S)`). -/
theorem bot_mem_over_emptyBase :
    (⊥ : Sieve (Over.mk (𝟙 emptyBase))) ∈ J.over emptyBase (Over.mk (𝟙 emptyBase)) := by
  rw [J, GrothendieckTopology.mem_over_iff, map_bot,
    GrothendieckTopology.mem_over_iff, map_bot]
  exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology
    (P := @AlgebraicGeometry.Etale) (X := emptyBase.left)

/-- **The hom presheaf of `Q` is not a sheaf on the empty base.** -/
theorem not_isSheaf_empty :
    ¬ Presheaf.IsSheaf (J.over emptyBase) (Q.presheafHom emptyObj emptyObj) := by
  intro h
  have hsub := subsingleton_of_bot_mem emptyObj emptyObj bot_mem_over_emptyBase h
  have hsub' : Subsingleton (HomFormS emptyBase emptyObj emptyObj
      (Opposite.op (Over.mk (𝟙 emptyBase)))) :=
    Eq.mp (congrArg Subsingleton
      (presheafHom_obj_eqS emptyBase emptyObj emptyObj
        (Opposite.op (Over.mk (𝟙 emptyBase))))) hsub
  haveI hsubX : Subsingleton (emptyBase ⟶ X) :=
    subsingleton_over_hom (by infer_instance) X
  have hφ : ∀ g : SignGroup,
      ((𝟙 emptyBase) ≫ pt emptyObj) ≫ S2882A6Aut g = (𝟙 emptyBase) ≫ pt emptyObj := by
    intro g
    rw [Category.id_comp]
    exact Subsingleton.elim _ _
  haveI := hsub'
  have h1 : (⟨1, hφ 1⟩ : HomFormS emptyBase emptyObj emptyObj
        (Opposite.op (Over.mk (𝟙 emptyBase)))) =
      ⟨Multiplicative.ofAdd (1 : ZMod 2), hφ _⟩ := Subsingleton.elim _ _
  have hval : (1 : SignGroup) = Multiplicative.ofAdd (1 : ZMod 2) := congrArg Subtype.val h1
  have hone : (1 : SignGroup) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by
    intro hh
    have h' : (0 : ZMod 2) = 1 := congrArg Multiplicative.toAdd hh
    exact absurd h' (by decide)
  exact hone hval

/-- **A1 fails**: the A6 pointwise pseudofunctor is not a prestack for the etale topology. -/
theorem S2975b_not_isPrestack :
    ¬ S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology K) := by
  intro h
  exact not_isSheaf_empty (h.isSheaf emptyObj emptyObj)

/-- **The A6 `IsStack` target fails as well**, since a stack is a prestack. -/
theorem S2975b_not_isStack :
    ¬ S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K) :=
  fun h => S2975b_not_isPrestack h.toIsPrestack

end EmptyBase

#print axioms presheafHom_obj_eq
#print axioms subsingleton_of_bot_mem
#print axioms not_isSheaf_empty
#print axioms S2975b_not_isPrestack
#print axioms S2975b_not_isStack

end LeanFormal.IUT.XiFPaper.S2975bA6QPresheafHomSheaf