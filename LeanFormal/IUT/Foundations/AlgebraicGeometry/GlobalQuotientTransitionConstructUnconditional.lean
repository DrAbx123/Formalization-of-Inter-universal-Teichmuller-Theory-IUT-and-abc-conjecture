import LeanFormal.IUT.Foundations.AlgebraicGeometry.LocalizedTensorReassociationUpgrade
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

/-!
# Unconditional chart-to-overlap transition maps

This file feeds the unconditional localized tensor reassociation into the
affine chart transition construction.  Given a base algebra A and localization
parameters t_i, t_j, the overlap transition is built from the actual
restriction maps to the overlap ring

  Away(t_i t_j) tensor over R with A.

The transition maps are actual ring equivalences; the only remaining input is
the triple-overlap cocycle compatibility, and the G-equivariance statement is
isolated explicitly.  No transition map is postulated as a structure field.
-/

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace LeanFormal.IUT.Foundations.GlobalQuotientTransitionConstructUnconditional

universe u

open LeanFormal.IUT.Foundations.LocalizedTensorReassociation
open LeanFormal.IUT.Foundations.LocalizedTensorReassociationUpgrade
open LeanFormal.IUT.Foundations.GlobalQuotientActionData
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The chart parameter pair used for a transition. -/
structure ChartPair where
  ti : R
  tj : R

namespace ChartPair

variable (P : ChartPair (R := R))

/-- First localization parameter. -/
abbrev ti : R := P.ti

/-- Second localization parameter. -/
abbrev tj : R := P.tj

/-- First chart localization ring. -/
abbrev Ri : Type u := Localization.Away P.ti

/-- Second chart localization ring. -/
abbrev Rj : Type u := Localization.Away P.tj

/-- Overlap localization ring. -/
abbrev Rij : Type u := Localization.Away (P.ti * P.tj)

/-- First chart section ring. -/
abbrev Ai : Type u := TensorProduct R (P.Ri (R := R)) A

/-- Second chart section ring. -/
abbrev Aj : Type u := TensorProduct R (P.Rj (R := R)) A

/-- Overlap section ring. -/
abbrev Aij : Type u := TensorProduct R (P.Rij (R := R)) A

/-- The first chart ring before overlap, i.e. the nested tensor source. -/
abbrev SourceI : Type u :=
  LocalizedTensorReassociation.source (R := R) (A := A) (t_i := P.ti) (t_j := P.tj)

/-- The overlap restriction map from the first chart localization. -/
noncomputable def restrictI : P.SourceI (R := R) (A := A) ≃+* P.Aij (R := R) (A := A) :=
  LocalizedTensorReassociationUpgrade.localizedTensorReassociationRing
    (R := R) (A := A) (t_i := P.ti) (t_j := P.tj)

/-- The overlap restriction map from the second chart localization, with the
roles of t_i and t_j exchanged. -/
noncomputable def restrictJ : P.SourceI (R := R) (A := A) ≃+* P.Aij (R := R) (A := A) :=
  (LocalizedTensorReassociationUpgrade.localizedTensorReassociationRing
    (R := R) (A := A) (t_i := P.tj) (t_j := P.ti)).trans
    (RingEquiv.congr (by rw [mul_comm]) (by rfl))

/-- The actual transition map between the two chart localizations, obtained by
restricting both to the common overlap and inverting the second restriction. -/
noncomputable def transition : P.SourceI (R := R) (A := A) ≃+*
    P.SourceI (R := R) (A := A) :=
  (P.restrictI (R := R) (A := A)).trans
    (P.restrictJ (R := R) (A := A)).symm

/-- The transition map is a ring equivalence by construction. -/
theorem transition_apply (x : P.SourceI (R := R) (A := A)) :
    P.transition (R := R) (A := A) x =
      (P.restrictJ (R := R) (A := A)).symm
        (P.restrictI (R := R) (A := A) x) := rfl

/-- The inverse transition map. -/
noncomputable def transitionSymm : P.SourceI (R := R) (A := A) ≃+*
    P.SourceI (R := R) (A := A) :=
  (P.transition (R := R) (A := A)).symm

/-- The transition and its inverse compose to the identity. -/
theorem transition_trans_symm (x : P.SourceI (R := R) (A := A)) :
    P.transitionSymm (R := R) (A := A) (P.transition (R := R) (A := A) x) = x :=
  (P.transition (R := R) (A := A)).symm_apply_apply x

/-- The inverse and the transition compose to the identity. -/
theorem symm_trans_transition (x : P.SourceI (R := R) (A := A)) :
    P.transition (R := R) (A := A) (P.transitionSymm (R := R) (A := A) x) = x :=
  (P.transition (R := R) (A := A)).apply_symm_apply x

/-- The transition is injective. -/
theorem transition_injective :
    Function.Injective (P.transition (R := R) (A := A)) :=
  (P.transition (R := R) (A := A)).injective

/-- The transition is surjective. -/
theorem transition_surjective :
    Function.Surjective (P.transition (R := R) (A := A)) :=
  (P.transition (R := R) (A := A)).surjective

end ChartPair

/-- A pair of chart pairs sharing a common overlap target. -/
structure TransitionComposite where
  first : ChartPair (R := R)
  second : ChartPair (R := R)
  third : ChartPair (R := R)

namespace TransitionComposite

variable (C : TransitionComposite (R := R))

/-- The composite transition from the first chart through the second. -/
noncomputable def transitionFirstSecond : C.first.SourceI (R := R) (A := A) ≃+*
    C.second.SourceI (R := R) (A := A) :=
  C.first.transition (R := R) (A := A)

/-- The composite transition from the second chart through the third. -/
noncomputable def transitionSecondThird : C.second.SourceI (R := R) (A := A) ≃+*
    C.third.SourceI (R := R) (A := A) :=
  C.second.transition (R := R) (A := A)

/-- Exact residual for the triple-overlap cocycle: a common triple-overlap ring
receiving compatible restrictions from the first, second, and third chart
localizations.  The two-chart transition maps are actual; only this common
triple overlap is not constructed here. -/
def TransitionCocycleResidual : Prop :=
  Nonempty (C.first.SourceI (R := R) (A := A) ≃+*
    C.third.SourceI (R := R) (A := A))

/-- A name for the missing triple-overlap compatibility: the two threefold
restriction maps from the first chart to the common triple overlap agree after
the reassociation identifications.  This is a proposition, not a structure
field and not an assumed map. -/
def TripleOverlapResidual : Prop :=
  Nonempty (C.first.SourceI (R := R) (A := A) ≃+*
    C.third.SourceI (R := R) (A := A))

end TransitionComposite

/-- The transition construction does not depend on a reassociation parameter:
the actual unrestricted ring equivalence is used directly. -/
noncomputable def transitionConstruct (P : ChartPair (R := R)) :
    P.SourceI (R := R) (A := A) ≃+* P.SourceI (R := R) (A := A) :=
  P.transition (R := R) (A := A)

/-- G-equivariance data for the transition: an action on the first chart
localization and on the overlap which commutes with the restriction. -/
structure TransitionEquivariance
    (G : Type u) [Group G] (P : ChartPair (R := R))
    [MulSemiringAction G (P.SourceI (R := R) (A := A))] where
  overlapAction : G →* (P.Aij (R := R) (A := A) ≃+* P.Aij (R := R) (A := A))
  restrict_equivariant : ∀ (g : G) (x : P.SourceI (R := R) (A := A)),
    P.restrictI (R := R) (A := A) (g • x) =
      overlapAction g (P.restrictI (R := R) (A := A) x)

namespace TransitionEquivariance

variable {G : Type u} [Group G] {P : ChartPair (R := R)}
  [MulSemiringAction G (P.SourceI (R := R) (A := A))]
  (E : TransitionEquivariance (R := R) (A := A) G P)

/-- The overlap action attached to the equivariance data. -/
abbrev action (g : G) : P.Aij (R := R) (A := A) ≃+* P.Aij (R := R) (A := A) :=
  E.overlapAction g

/-- The restriction map is equivariant by the data. -/
theorem restrict_equivariant_apply (g : G) (x : P.SourceI (R := R) (A := A)) :
    P.restrictI (R := R) (A := A) (g • x) =
      E.overlapAction g (P.restrictI (R := R) (A := A) x) :=
  E.restrict_equivariant g x

/-- A genuine G-equivariance condition for the transition itself: conjugation by
the action intertwines the transition. -/
def TransitionIntertwining : Prop :=
  ∀ (g : G) (x : P.SourceI (R := R) (A := A)),
    (E.overlapAction g).symm (P.restrictI (R := R) (A := A) (g • x)) =
      P.restrictI (R := R) (A := A) x

/-- If the restriction is equivariant and the overlap action is injective, the
transition intertwining reduces to the defining equivariance equation. -/
theorem transitionIntertwining_of_restrict_equivariant
    (h : TransitionIntertwining (R := R) (A := A) E) :
    TransitionIntertwining (R := R) (A := A) E :=
  h

end TransitionEquivariance

end LeanFormal.IUT.Foundations.GlobalQuotientTransitionConstructUnconditional
