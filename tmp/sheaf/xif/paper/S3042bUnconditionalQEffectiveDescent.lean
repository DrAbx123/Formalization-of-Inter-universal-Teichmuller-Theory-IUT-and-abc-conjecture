import tmp.sheaf.xif.paper.S2976bA6QDescentGluing
import tmp.sheaf.xif.paper.S3037cBottomNotCoveringConcrete
import tmp.sheaf.xif.paper.S2811IsPrestackActual
import tmp.sheaf.xif.paper.S2893A6QIsStackActual
import Mathlib.AlgebraicGeometry.Limits
noncomputable section
open CategoryTheory Opposite
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2976bA6QDescentGluing
open LeanFormal.IUT.XiFPaper.S3037cBottomNotCoveringConcrete
open LeanFormal.IUT.XiFPaper.S3037BottomNotCovering
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
open LeanFormal.IUT.XiFPaper.S3037NonemptyHne
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2811IsPrestackActual
open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3042bUnconditionalQEffectiveDescent

abbrev K : Type := S2882A6PointwisePseudofunctorActual.K
local instance : Field K := S2847A6.fieldF
local instance : NumberField K := S2847A6.numberFieldF
abbrev X : Iut.SchemeOverField K := S2844D6F6BaseChangeActual.S2844X
abbrev Q : Iut.EtaleStackPseudofunctor K := S2882A6Q
local instance : DecidableEq K := Classical.decEq _
local instance smulPoint (Y : Iut.SchemeOverField K) :
    SMul SignGroup (Y ⟶ X) :=
  S2882A6PointSMul (LocallyDiscrete.mk (op Y))
local instance mulActionPoint (Y : Iut.SchemeOverField K) :
    MulAction SignGroup (Y ⟶ X) :=
  S2882A6PointMulAction (LocallyDiscrete.mk (op Y))

/-- The bottom sieve is not covering on the big etale site when the base is nonempty. -/
theorem S3042b_bottom_not_mem (U : Iut.SchemeOverField K) (hU : Nonempty U.left) :
    ((⊥ : Sieve U) ∉ Iut.SchemeOverField.etaleTopology K U) := by
  let U' : S3026NonemptyScheme := ⟨U, hU⟩
  have hns : ¬ Subsingleton
      ((yoneda.obj (S3037cX U')).obj (Opposite.op U)) := by
    intro hsub
    exact S3037cInl_ne_inr U' hU
      (hsub.elim (S3037cInl U') (S3037cInr U'))
  intro hbot
  exact hns (S3037_subsingleton_of_bot_mem
    (P := yoneda.obj (S3037cX U'))
    (S2811_yoneda_isSheaf K (S3037cX U')) hbot)

/-- Every covering sieve on a nonempty base has a nonempty index category. -/
theorem S3042b_hne_of_nonempty (U : Iut.SchemeOverField K) (hU : Nonempty U.left)
    (R : Sieve U) (hR : R ∈ Iut.SchemeOverField.etaleTopology K U) :
    Nonempty R.arrows.category := by
  by_contra hne
  apply S3042b_bottom_not_mem U hU
  have hRbot : R = ⊥ := by
    ext Y f
    constructor
    · intro hf
      exact False.elim (hne ⟨⟨Over.mk f, hf⟩⟩)
    · intro hf
      exact False.elim hf
  simpa [hRbot] using hR

/-- The empty-index case of effective descent: over an empty base scheme the global
action-groupoid object exists by initiality of the empty scheme, and all index
comparisons are vacuous. -/
theorem S3042b_essSurj_empty {U : Iut.SchemeOverField K} {R : Sieve U}
    (hempty : IsEmpty R.arrows.category) (hU : IsEmpty U.left) :
    (Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj := by
  haveI : IsEmpty R.arrows.category := hempty
  haveI : IsEmpty U.left := hU
  let pm : U ⟶ X :=
    Over.homMk ((isInitialOfIsEmpty (X := U.left)).to X.left)
      ((isInitialOfIsEmpty (X := U.left)).hom_ext _ _)
  let M : Q.obj (LocallyDiscrete.mk (op U)) :=
    (pm : ActionCategory SignGroup (U ⟶ X))
  refine ⟨fun D => ⟨M, ⟨?_⟩⟩⟩
  refine Pseudofunctor.DescentData.isoMk (fun i => isEmptyElim i) ?_
  intro Y q i1 i2
  exact isEmptyElim i1

/-- **Unconditional effective descent for the A6 pointwise Q.** -/
theorem S3042b_QEffectiveDescent : S2893A6QEffectiveDescent := by
  intro U R hR
  by_cases hne : Nonempty R.arrows.category
  · obtain ⟨i0⟩ := hne
    exact S2976b_essSurj_nonempty i0 hR
  · haveI : IsEmpty R.arrows.category := not_nonempty_iff.mp hne
    have hUempty : IsEmpty U.left := by
      apply not_nonempty_iff.mp
      intro hU
      exact hne (S3042b_hne_of_nonempty U hU R hR)
    exact S3042b_essSurj_empty (not_nonempty_iff.mp hne) hUempty

#check S3042b_bottom_not_mem
#check S3042b_hne_of_nonempty
#check S3042b_essSurj_empty
#check S3042b_QEffectiveDescent
#print axioms S3042b_QEffectiveDescent

end LeanFormal.IUT.XiFPaper.S3042bUnconditionalQEffectiveDescent
