import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Quotient consumer for the actual regular permutation action

This file consumes the production regular-permutation cocone (not the constant
action provider) and packages its universal property for qside/primespine.
The IsColimit proof is an explicit input; no colimit is fabricated here.
-/
namespace ABCBridge.RegularPermutationQuotientConsumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open AffineLocalQuotientGluingConstruct

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

/-- Data package: the production regular-permutation cocone together with an
actual `IsColimit` proof. -/
structure RegularPermutationQuotientData where
  cocone : Cocone (regularPermutationActionFunctor R G)
  isColimit : IsColimit cocone

/-- The production regular-permutation cocone, once its `IsColimit` is supplied. -/
noncomputable def regularPermutationQuotientData
    (h : IsColimit (regularPermutationCocone R G)) :
    RegularPermutationQuotientData R G :=
  ⟨regularPermutationCocone R G, h⟩

/-- A supplied colimit proof gives `HasColimit` for the actual regular action. -/
noncomputable def regularPermutationHasColimit
    (h : IsColimit (regularPermutationCocone R G)) :
    HasColimit (regularPermutationActionFunctor R G) :=
  HasColimit.mk ⟨regularPermutationCocone R G, h⟩

/-- Desc map out of the regular quotient for an arbitrary cocone. -/
noncomputable def regularPermutationCoconeDesc
    (h : IsColimit (regularPermutationCocone R G))
    (c : Cocone (regularPermutationActionFunctor R G)) :
    (regularPermutationCocone R G).pt ⟶ c.pt :=
  h.desc c

theorem regularPermutationCoconeDesc_fac
    (h : IsColimit (regularPermutationCocone R G))
    (c : Cocone (regularPermutationActionFunctor R G))
    (j : SingleObj G) :
    (regularPermutationCocone R G).ι.app j ≫
        regularPermutationCoconeDesc (R := R) (G := G) h c =
      c.ι.app j :=
  h.fac c j

theorem regularPermutationCoconeDesc_uniq
    (h : IsColimit (regularPermutationCocone R G))
    (c : Cocone (regularPermutationActionFunctor R G))
    (m : (regularPermutationCocone R G).pt ⟶ c.pt)
    (hm : ∀ j : SingleObj G,
      (regularPermutationCocone R G).ι.app j ≫ m = c.ι.app j) :
    m = regularPermutationCoconeDesc (R := R) (G := G) h c :=
  h.uniq c m hm

end ABCBridge.RegularPermutationQuotientConsumer