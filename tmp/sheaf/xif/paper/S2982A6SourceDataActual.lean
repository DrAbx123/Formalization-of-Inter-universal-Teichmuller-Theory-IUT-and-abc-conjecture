import tmp.sheaf.xif.paper.S2883UniqueFromClassification
import tmp.sheaf.xif.paper.S2978ClassificationInputActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification
open LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
open LeanFormal.IUT.XiFPaper.S2879NontrivialStackAutoActual
open LeanFormal.IUT.XiFPaper.S2876NontrivialAlphaActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2978ClassificationInputActual
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2982A6SourceDataActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-!
## S2982: source data for `S2883Inputs`

`S2883Inputs` has exactly two fields, `classification` and
`underlying_ne_id_iff`; it lives in `Prop`, so it is a conjunction of two
statements and carries no data.

Main results below:
* `S2982_underlying_id`:  the underlying scheme map of the identity is the
  identity (the S1742 computation, reused from S2879);
* `S2982_underlying_ne_id_of_ne`: the forward direction of the S2883
  equivalence is free;
* `S2982_underlying_ne_id_iff_iff_reflects`: the whole S2883 equivalence is
  *equivalent* to the single reflection-of-identity statement
  `S2982UnderlyingReflectsId`, so the field adds exactly one obligation;
* `S2982_app_eq_of_underlying_eq`: an orbicurve endomorphism with identity
  underlying scheme map has identity `app` component;
* `S2982_rigidity` + `S2982_reflectsId`: the residual 2-categorical rigidity
  (a strong transformation is determined by its `app` component, because the
  target categories are discrete) is proved from the app computation, so
  `underlying_ne_id_iff` is **unconditional**;
* `S2982Inputs_of`: `S2883Inputs` from the classification alone.
-/

/-- The underlying scheme endomorphism of the identity orbicurve morphism is
the identity.  This is the S1742 computation `𝟙 S ≫ 𝟙 S = 𝟙 S`. -/
theorem S2982_underlying_id :
    S2877Underlying
        (Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) =
      𝟙 S2844D6F6BaseChangeActual.S2844X :=
  S2879_homOfStrongTrans_id

/-- Free direction of `S2883Inputs.underlying_ne_id_iff`: if the underlying
scheme morphism is nontrivial then the orbicurve morphism is nontrivial.
Contrapositive of `S2982_underlying_id`; no extra input. -/
theorem S2982_underlying_ne_id_of_ne
    (inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (h : S2877Underlying inv ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X) :
    inv ≠ Iut.HyperbolicOrbicurve.Hom.id
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve := by
  intro hinv
  exact h (by rw [hinv]; exact S2982_underlying_id)

/-- **The exact remaining mathematical input for the second field of
`S2883Inputs`.**  The S1742 comparison `S2877Underlying` must reflect
identity: an orbicurve endomorphism whose underlying scheme endomorphism is the
identity is the identity endomorphism. -/
def S2982UnderlyingReflectsId : Prop :=
  ∀ inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
    S2877Underlying inv = 𝟙 S2844D6F6BaseChangeActual.S2844X →
      inv = Iut.HyperbolicOrbicurve.Hom.id
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve

/-- **Reduction of the whole S2883 field to one statement.**  The full
equivalence `underlying ≠ 𝟙 ↔ inv ≠ id` is *equivalent* to
`S2982UnderlyingReflectsId`: the forward direction is free, so the field adds
exactly one new obligation, namely reflection of identity. -/
theorem S2982_underlying_ne_id_iff_iff_reflects
    :
    (∀ inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
      S2877Underlying inv ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X ↔
        inv ≠ Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) ↔
      S2982UnderlyingReflectsId := by
  constructor
  · intro h inv hinv
    by_contra hne
    exact (h inv).mpr hne hinv
  · intro hf inv
    exact ⟨S2982_underlying_ne_id_of_ne inv, fun hne h1 => hne (hf inv h1)⟩

/-! ## The app component of a strong transformation with identity underlying map -/

/-- The S1742 `app` component of the identity scheme morphism is the identity
functor. -/
theorem S2982_app_id
    (a : LocallyDiscrete (Iut.SchemeOverField S2847A6.F)ᵒᵖ) :
    S1742App (F := S2847A6.F) (S := S2844D6F6BaseChangeActual.S2844X)
        (T := S2844D6F6BaseChangeActual.S2844X)
        (𝟙 S2844D6F6BaseChangeActual.S2844X) a =
      𝟙 ((S1742YS (F := S2847A6.F) S2844D6F6BaseChangeActual.S2844X).obj a) := by
  apply CategoryTheory.Cat.ext
  apply Discrete.functor_ext
  intro P
  exact congrArg Discrete.mk (Category.comp_id P)

/-- **First step of reflection of identity.**  If the underlying scheme
endomorphism is the identity then the `app` component of the strong
transformation is the identity functor at every test object. -/
theorem S2982_app_eq_of_underlying_eq
    (inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (h : S2877Underlying inv = 𝟙 S2844D6F6BaseChangeActual.S2844X) :
    ∀ a : LocallyDiscrete (Iut.SchemeOverField S2847A6.F)ᵒᵖ,
      inv.app a =
        𝟙 ((S1742YS (F := S2847A6.F) S2844D6F6BaseChangeActual.S2844X).obj a) := by
  intro a
  have h' : S1742HomOfStrongTrans (F := S2847A6.F) inv =
      𝟙 S2844D6F6BaseChangeActual.S2844X := h
  have h2 : S1742App (F := S2847A6.F) (S := S2844D6F6BaseChangeActual.S2844X)
      (T := S2844D6F6BaseChangeActual.S2844X)
      (S1742HomOfStrongTrans (F := S2847A6.F) inv) a = inv.app a :=
    S1742AppEq (F := S2847A6.F) inv a
  rw [h'] at h2
  exact h2.symm.trans (S2982_app_id a)

/-! ## 2-categorical rigidity

A strong transformation between the representable pseudofunctors of `S2844X`
is determined by its `app` component.  The proof uses that every target
category is discrete, so the 2-cells (natural transformations) and the
coherence proofs in `naturality` are subsingletons. -/

/-- **The residual 2-categorical statement**: the `app` component determines a
strong transformation of the representable pseudofunctor of `S2844X`. -/
def S2982StrongTransRigidity : Prop :=
  ∀ eta : Pseudofunctor.StrongTrans
      (S1742YS (F := S2847A6.F) S2844D6F6BaseChangeActual.S2844X)
      (S1742YS (F := S2847A6.F) S2844D6F6BaseChangeActual.S2844X),
    (∀ a : LocallyDiscrete (Iut.SchemeOverField S2847A6.F)ᵒᵖ,
        eta.app a =
          𝟙 ((S1742YS (F := S2847A6.F) S2844D6F6BaseChangeActual.S2844X).obj a)) →
      eta = Pseudofunctor.StrongTrans.id
        (S1742YS (F := S2847A6.F) S2844D6F6BaseChangeActual.S2844X)

/-! The rigidity is proved by dependent elimination: destruct the strong
transformation, substitute the `app` component by the identity `app` obtained
from the hypothesis (via `funext`), and close the resulting structure equality
by congruence.  The remaining field comparisons are the coherence proofs, which
are propositions. -/
theorem S2982_rigidity : S2982StrongTransRigidity := by
  intro eta happ
  cases eta with
  | mk app nat p1 p2 p3 =>
    have happ' : app =
        (Pseudofunctor.StrongTrans.id
          (S1742YS (F := S2847A6.F) S2844D6F6BaseChangeActual.S2844X)).app :=
      funext happ
    subst happ'
    congr 1

/-- **`underlying_ne_id_iff` is unconditional**: reflection of identity follows
from the rigidity and the app computation. -/
theorem S2982_reflectsId : S2982UnderlyingReflectsId := by
  intro inv h
  have hrig := S2982_rigidity inv (S2982_app_eq_of_underlying_eq inv h)
  exact hrig

/-- **`S2883Inputs` from the classification alone.**  The second field is
discharged unconditionally. -/
theorem S2982Inputs_of
    (hclass : S2877OrderTwoAutClassification) : S2883Inputs where
  classification := hclass
  underlying_ne_id_iff := fun inv =>
    ⟨S2982_underlying_ne_id_of_ne inv, fun hne h1 => hne (S2982_reflectsId inv h1)⟩

/-- The consumer `S2877_unique_of_classification`, with the nontriviality of
the underlying map as the only nontriviality hypothesis. -/
theorem S2982_unique_of
    (hclass : S2877OrderTwoAutClassification)
    (inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (hsq : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve))
    (hnt : inv ≠ Iut.HyperbolicOrbicurve.Hom.id
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) :
    Nonempty
      (Iut.HyperbolicOrbicurve.Hom.TwoIso inv (S2857StackAuto alphaOverS2844)) :=
  S2877_unique_of_classification hclass inv hsq
    (fun h1 => hnt (S2982_reflectsId inv h1))

/-- The `≠ 1` branch of the classification is forced to be the chart alpha
automorphism: for a nontrivial order-two scheme automorphism the classification
returns `alphaOverS2844` outright.  This is the form the consumer uses. -/
theorem S2982_classification_alt
    (hclass : S2877OrderTwoAutClassification)
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hne : β ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X) :
    β = alphaOverS2844 := by
  rcases hclass β hβ with hid | halpha
  · exact absurd hid hne
  · exact halpha

/-- The two alternatives in the classification are distinct, so the dichotomy is
not degenerate. -/
theorem S2982_alt_distinct :
    alphaOverS2844 ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X :=
  S2876_alphaOverS2844_ne_id

#check S2982_underlying_id
#check S2982_underlying_ne_id_of_ne
#check S2982UnderlyingReflectsId
#check S2982_underlying_ne_id_iff_iff_reflects
#check S2982_app_id
#check S2982_app_eq_of_underlying_eq
#check S2982StrongTransRigidity
#check S2982_rigidity
#check S2982_reflectsId
#check S2982Inputs_of
#check S2982_unique_of
#check S2982_classification_alt
#check S2982_alt_distinct
#print axioms S2982_underlying_id
#print axioms S2982_underlying_ne_id_iff_iff_reflects
#print axioms S2982_app_id
#print axioms S2982_app_eq_of_underlying_eq
#print axioms S2982_rigidity
#print axioms S2982_reflectsId
#print axioms S2982Inputs_of
#print axioms S2982_unique_of
#print axioms S2982_classification_alt
#print axioms S2982_alt_distinct

end LeanFormal.IUT.XiFPaper.S2982A6SourceDataActual
end
