/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2028
-/
import tmp.sheaf.xif.paper.S2023SourceSchemeActual
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# S2028: the cover source *is* representable

## The result

S2023 reduced the corrected identity repair to the geometric statement

  S2018SourceSchemeAll :
    every finite-etale cover source is quasi-equivalent to y Q for a scheme Q.

This file proves it.

## The construction

For a cover A : S1728Cover let

* S_A = S1733Model A be the affine finite-etale model obtained from the
  identity-point base change, with structure map p : S_A -> Spec R';
* t = S1756ToSource A : y(S_A) -> A.source the comparison 1-cell;
* l = S1743Lift A : A.source -> y(S_A) the lift of the identity cone.

The weak two-pullback witness gives, unconditionally, the section

  l ; t ~ id A.source     (S1784Section).

Consequently the endomorphism

  e_S := 2-Yoneda-evaluation of (t ; l) = S1756End A

of the scheme S_A is idempotent (S1756End_idempotent) and is a morphism
over the base (S1756End_projection).  Let Q be its equalizer with the
identity in the category SchemeOverField K = Over (Spec K):

  Q := equalizer (S1756End A) (id S_A).

Write i : Q -> S_A for the equalizer inclusion.  The idempotence makes e_S
factor through Q:

  q := equalizer.lift (S1756End A) h_idem : S_A -> Q,
  q ; i = e_S,
  i ; q = id Q.

The last equation follows from the equalizer universal property: both
(i ; q) ; i and id Q ; i equal i.

At the level of stacks this is exactly a splitting of the source as a retract
of the finite-etale affine model.  Put

  U := y(i) ; t : y(Q) -> A.source,
  V := l ; y(q) : A.source -> y(Q).

Using q ; i = e_S, i ; q = id Q and l ; t ~ id A.source, the two
composites are 2-isomorphic to the identities:

  U ; V ~ id (y Q),     V ; U ~ id (A.source).

Hence y(Q) and the cover source are quasi-equivalent, and the apex Q is an
actual scheme.  The point is that the canonical comparison t need not itself
be an equivalence; the source is a *retract* of the larger finite-etale model,
and the equalizer of the idempotent e_S is the representing scheme of that
retract.  This is why the previously recorded missing unit 2-cell
t ; l ~ id (y S_A) is not needed for source representability.

## Consequences

* S2028SourceSchemeAll : S2018SourceSchemeAll
* S2028IdentityRepairAll : S2015IdentityRepairAll
* S2028FirstMissing : S2018FirstMissing
* S2028UniqFirstMissing : S2001UniqFirstMissing

Thus the exact residual of S2023 is closed.  No sorry, no new axiom, no
Shrink/ULift/PUnit, no fake scheme, equivalence or 2-cell.  Axiom
footprint: propext, Classical.choice, Quot.sound (audit at the end).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2028SourceSchemeActual

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual
open LeanFormal.IUT.XiFPaper.S2015FullPullbackActual
open LeanFormal.IUT.XiFPaper.S2018IdentityRepairActual
open LeanFormal.IUT.XiFPaper.S2023SourceSchemeActual

/-! ## 1. The idempotent endomorphism and its equalizer -/

/-- The idempotent endomorphism S1756End A of the affine finite-etale model,
written in this file's namespace.  It is already a morphism of
SchemeOverField S1726K = Over (Spec K) by construction. -/
noncomputable abbrev S2028End (A : S1728Cover) :
    S1733Model A ⟶ S1733Model A :=
  S1756End A

/-- The representing scheme of the fixed-point retract: the equalizer of the
idempotent S1756End A with the identity of the affine model.  It is an object
of SchemeOverField S1726K, hence an actual scheme over the base. -/
noncomputable abbrev S2028Q (A : S1728Cover) : SchemeOverField S1726K :=
  equalizer (S1756End A) (𝟙 (S1733Model A))

/-- The equalizer inclusion Q -> S_A. -/
noncomputable abbrev S2028I (A : S1728Cover) :
    S2028Q A ⟶ S1733Model A :=
  equalizer.ι _ _

/-- The factorisation S_A -> Q of the idempotent through its equalizer. -/
noncomputable abbrev S2028Qm (A : S1728Cover) :
    S1733Model A ⟶ S2028Q A :=
  equalizer.lift (S1756End A) (by
    exact S1756End_idempotent A)

/-- **The retraction equation.**  The equalizer of an idempotent and the
identity is a split monomorphism: the factorisation q is a retraction of the
inclusion i. -/
theorem S2028I_comp_Qm (A : S1728Cover) :
    S2028I A ≫ S2028Qm A = 𝟙 (S2028Q A) := by
  apply equalizer.hom_ext
  rw [Category.assoc,
    show S2028Qm A ≫ S2028I A = S1756End A from equalizer.lift_ι _ _]
  rw [equalizer.condition]
  simp

/-- **The factorisation equation.**  The composite q ; i is the idempotent
S1756End A whose equalizer defines Q. -/
theorem S2028Qm_comp_I (A : S1728Cover) :
    S2028Qm A ≫ S2028I A = S1756End A :=
  equalizer.lift_ι _ _

/-! ## 2. The 2-Yoneda evaluations -/

/-- The strong transformation y(Q) -> y(S_A) induced by the inclusion. -/
noncomputable abbrev S2028ITrans (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743Y (S2028Q A)) (S1743Y (S1733Model A)) :=
  S1743StrongTransOfHom (S2028I A)

/-- The strong transformation y(S_A) -> y(Q) induced by the factorisation. -/
noncomputable abbrev S2028QmTrans (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743Y (S1733Model A)) (S1743Y (S2028Q A)) :=
  S1743StrongTransOfHom (S2028Qm A)

/-- 2-Yoneda evaluation of y(i). -/
theorem S2028ITrans_eval (A : S1728Cover) :
    S1743YonedaEval (S2028Q A) (S1733Model A) (S2028ITrans A) = S2028I A := by
  change S1742HomOfStrongTrans (S1742StrongTransOfHom (S2028I A)) = S2028I A
  exact S1742HomOfStrongTrans_strongTransOfHom (S2028I A)

/-- 2-Yoneda evaluation of y(q). -/
theorem S2028QmTrans_eval (A : S1728Cover) :
    S1743YonedaEval (S1733Model A) (S2028Q A) (S2028QmTrans A) = S2028Qm A := by
  change S1742HomOfStrongTrans (S1742StrongTransOfHom (S2028Qm A)) = S2028Qm A
  exact S1742HomOfStrongTrans_strongTransOfHom (S2028Qm A)

/-- The evaluation of y(q) ; y(i) is the idempotent S1756End A. -/
theorem S2028QmI_eval (A : S1728Cover) :
    S1743YonedaEval (S1733Model A) (S1733Model A)
      ((S2028QmTrans A).vcomp (S2028ITrans A)) = S1756End A := by
  rw [S1743YonedaEval_vcomp, S2028QmTrans_eval, S2028ITrans_eval,
    S2028Qm_comp_I]

/-- The evaluation of y(i) ; y(q) is the identity of Q. -/
theorem S2028IQm_eval (A : S1728Cover) :
    S1743YonedaEval (S2028Q A) (S2028Q A)
      ((S2028ITrans A).vcomp (S2028QmTrans A)) = 𝟙 (S2028Q A) := by
  rw [S1743YonedaEval_vcomp, S2028ITrans_eval, S2028QmTrans_eval,
    S2028I_comp_Qm]

/-- y(q) ; y(i) is 2-isomorphic to the idempotent t ; l. -/
theorem S2028QmI_iso (A : S1728Cover) :
    Nonempty (Pseudofunctor.StrongTrans.vcomp (S2028QmTrans A) (S2028ITrans A) ≅
      S1784EndTrans A) := by
  apply S1756IsoOfEvalEq
  rw [S2028QmI_eval]
  rfl

/-- The 2-isomorphism y(q) ; y(i) ~ t ; l. -/
noncomputable def S2028Beta (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2028QmTrans A) (S2028ITrans A))
      (S1784EndTrans A) :=
  (S2028QmI_iso A).some

/-- y(i) ; y(q) is 2-isomorphic to the identity of y(Q). -/
noncomputable def S2028Alpha (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2028ITrans A) (S2028QmTrans A))
      (Pseudofunctor.StrongTrans.id (S1743Y (S2028Q A))) :=
  (S1756IsoOfEvalEq (S2028Q A) (S2028Q A) _ _
    (by rw [S2028IQm_eval, S1756YonedaEval_id])).some

/-! ## 3. The two inverse 1-cells -/

/-- U = y(i) ; t : y(Q) -> A.source. -/
noncomputable abbrev S2028U (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743Y (S2028Q A)) (S1743Source A) :=
  (S2028ITrans A).vcomp (S1756ToSource A)

/-- V = l ; y(q) : A.source -> y(Q). -/
noncomputable abbrev S2028V (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743Source A) (S1743Y (S2028Q A)) :=
  (S1743Lift A).vcomp (S2028QmTrans A)

/-- **First triangle.**  V ; U is 2-isomorphic to the identity of the cover
source.  This uses only the unconditional section l ; t ~ id. -/
noncomputable def S2028Counit (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2028V A) (S2028U A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) :=
  calc
    Pseudofunctor.StrongTrans.vcomp (S2028V A) (S2028U A)
        ≅ Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
            (Pseudofunctor.StrongTrans.vcomp (S2028QmTrans A)
              (Pseudofunctor.StrongTrans.vcomp (S2028ITrans A)
                (S1756ToSource A))) :=
          S1756AssociatorIso _ _ _
    _ ≅ Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp (S2028QmTrans A) (S2028ITrans A))
            (S1756ToSource A)) :=
          S1756WhiskerLeftIso _ _ _ (S1756AssociatorIso _ _ _).symm
    _ ≅ Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
          (Pseudofunctor.StrongTrans.vcomp (S1784EndTrans A) (S1756ToSource A)) :=
          S1756WhiskerLeftIso _ _ _
            (S1756WhiskerRightIso _ _ _ (S2028Beta A))
    _ ≅ Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
            (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))) :=
          S1756WhiskerLeftIso _ _ _ (S1756AssociatorIso _ _ _)
    _ ≅ Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
            (Pseudofunctor.StrongTrans.id (S1743Source A))) :=
          S1756WhiskerLeftIso _ _ _
            (S1756WhiskerLeftIso _ _ _ (S1784Section A))
    _ ≅ Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A) :=
          S1756WhiskerLeftIso _ _ _ (S1756RightUnitorIso _)
    _ ≅ Pseudofunctor.StrongTrans.id (S1743Source A) := S1784Section A

/-- **Second triangle.**  U ; V is 2-isomorphic to the identity of y(Q).
The proof uses the splitting q ; i = e_S, i ; q = id Q of the idempotent. -/
noncomputable def S2028Unit (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2028U A) (S2028V A))
      (Pseudofunctor.StrongTrans.id (S1743Y (S2028Q A))) :=
  calc
    Pseudofunctor.StrongTrans.vcomp (S2028U A) (S2028V A)
        ≅ Pseudofunctor.StrongTrans.vcomp (S2028ITrans A)
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
              (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S2028QmTrans A))) :=
          S1756AssociatorIso _ _ _
    _ ≅ Pseudofunctor.StrongTrans.vcomp (S2028ITrans A)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
            (S2028QmTrans A)) :=
          S1756WhiskerLeftIso _ _ _ (S1756AssociatorIso _ _ _).symm
    _ ≅ Pseudofunctor.StrongTrans.vcomp (S2028ITrans A)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp (S2028QmTrans A) (S2028ITrans A))
            (S2028QmTrans A)) :=
          S1756WhiskerLeftIso _ _ _
            (S1756WhiskerRightIso _ _ _ (S2028Beta A).symm)
    _ ≅ Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S2028ITrans A) (S2028QmTrans A))
          (Pseudofunctor.StrongTrans.vcomp (S2028ITrans A) (S2028QmTrans A)) :=
          (S1756AssociatorIso _ _ _).symm |>.trans
            (S1756WhiskerRightIso _ _ _
              (S1756AssociatorIso _ _ _).symm) |>.trans
            (S1756AssociatorIso _ _ _)
    _ ≅ Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.id (S1743Y (S2028Q A)))
          (Pseudofunctor.StrongTrans.vcomp (S2028ITrans A) (S2028QmTrans A)) :=
          S1756WhiskerRightIso _ _ _ (S2028Alpha A)
    _ ≅ Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.id (S1743Y (S2028Q A)))
          (Pseudofunctor.StrongTrans.id (S1743Y (S2028Q A))) :=
          S1756WhiskerLeftIso _ _ _ (S2028Alpha A)
    _ ≅ Pseudofunctor.StrongTrans.id (S1743Y (S2028Q A)) :=
          S1756LeftUnitorIso _

/-! ## 4. Source representability -/

/-- The quasi-equivalence between the representable stack of the scheme Q and
the cover source. -/
noncomputable def S2028StackEquiv (A : S1728Cover) :
    S1756StackEquiv (S1743Y (S2028Q A)) (S1743Source A) where
  hom := S2028U A
  inv := S2028V A
  unit := S2028Unit A
  counit := S2028Counit A

/-- **Every cover source is representable by its fixed-point scheme Q.** -/
theorem S2028SourceScheme (A : S1728Cover) : S2018SourceScheme A :=
  ⟨S2028Q A, ⟨S2028StackEquiv A⟩⟩

/-- **S2018SourceSchemeAll is proved.** -/
theorem S2028SourceSchemeAll : S2018SourceSchemeAll :=
  fun A => S2028SourceScheme A

/-- S2023's named residual is inhabited: its statement is exactly
S2018SourceSchemeAll. -/
theorem S2028S2023FirstMissing : S2023FirstMissing :=
  S2028SourceSchemeAll

/-- The corrected identity-point presentation for one cover, now unconditional. -/
theorem S2028IdentityRepair (A : S1728Cover) : S2015IdentityRepair A :=
  S2023IdentityRepair_of_sourceScheme A (S2028SourceScheme A)

/-- **S2015IdentityRepairAll is proved.** -/
theorem S2028IdentityRepairAll : S2015IdentityRepairAll :=
  S2023IdentityRepairAll_of_sourceSchemeAll S2028SourceSchemeAll

/-- **S2018FirstMissing is proved.** -/
theorem S2028FirstMissing : S2018FirstMissing :=
  S2023FirstMissing_of_sourceSchemeAll S2028SourceSchemeAll

/-- **S2001UniqFirstMissing is proved.** -/
theorem S2028UniqFirstMissing : S2001UniqFirstMissing :=
  S2023UniqFirstMissing_of_sourceSchemeAll S2028SourceSchemeAll

/-- Every cover has discrete geometric fibres. -/
theorem S2028CoverFiberDiscrete (A : S1728Cover) : S2001CoverFiberDiscrete A :=
  S2023CoverFiberDiscrete_of_sourceScheme A (S2028SourceScheme A)

/-! ## 5. Checks and axiom audit -/

#check S2028End
#check S2028Q
#check S2028I
#check S2028Qm
#check S2028I_comp_Qm
#check S2028Qm_comp_I
#check S2028ITrans_eval
#check S2028QmTrans_eval
#check S2028QmI_iso
#check S2028Beta
#check S2028Alpha
#check S2028U
#check S2028V
#check S2028Counit
#check S2028Unit
#check S2028StackEquiv
#check S2028SourceScheme
#check S2028SourceSchemeAll
#check S2028S2023FirstMissing
#check S2028IdentityRepair
#check S2028IdentityRepairAll
#check S2028FirstMissing
#check S2028UniqFirstMissing
#check S2028CoverFiberDiscrete

#print axioms S2028I_comp_Qm
#print axioms S2028Qm_comp_I
#print axioms S2028ITrans_eval
#print axioms S2028QmTrans_eval
#print axioms S2028QmI_iso
#print axioms S2028Beta
#print axioms S2028Alpha
#print axioms S2028Counit
#print axioms S2028Unit
#print axioms S2028StackEquiv
#print axioms S2028SourceScheme
#print axioms S2028SourceSchemeAll
#print axioms S2028S2023FirstMissing
#print axioms S2028IdentityRepair
#print axioms S2028IdentityRepairAll
#print axioms S2028FirstMissing
#print axioms S2028UniqFirstMissing
#print axioms S2028CoverFiberDiscrete

end LeanFormal.IUT.XiFPaper.S2028SourceSchemeActual
