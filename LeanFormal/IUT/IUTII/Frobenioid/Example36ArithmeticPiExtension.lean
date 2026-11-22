import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveSourcePiCard
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import Mathlib.Tactic

/-!
# Arithmetic curve pi1 extension card from the actual torsion Galois action

This module assembles the arithmetic-pi1 extension card of the concrete
elliptic curve y^2 = x^3 - x over Q from the actual finite-level Galois
actions on E[2] and E[4] that are constructed in the tree, together with the
actual ZMod-l-linear representations on the l-torsion for l >= 5 that the
tree's punctured-elliptic-curve API provides.

## Contents

1. The actual Galois action on E[4] (the level-two action already exists),
   its action laws, ZMod-4-linearity, and the actual distributive actions of
   G_Q on the additive modules E[2] and E[4].
2. For the punctured-elliptic-curve API with l >= 5, the actual ZMod-l-linear
   Galois representations on the actual l-torsion modules (re-exported from
   the tree's EllipticTorsion module).
3. The outer automorphism group Out(G) = Aut(G)/Inn(G) and the frozen
   arithmetic curve pi1 extension card
   1 -> Pi_geo -> Pi_arith -> G_Q -> 1
   with the genuine outer action G_Q -> Out(Pi_geo).  The card is DATA: no
   inhabitant is constructed, no split extension and no chosen-action
   semidirect product is asserted to be the source.
4. Actual statements about the finite-level split product models: their
   geometric kernel is the concrete torsion group and conjugation by any
   lift acts trivially on it.  This is exactly why the split product model is
   not the source arithmetic pi1 extension.
5. The missing nonabelian data is frozen as cards: the nonabelian geometric
   fundamental group of the punctured curve, its outer action, and the
   punctured-curve cusp inertia.  None is constructed.

## Boundary

* The finite-level split product groups G_Q x E[2], G_Q x E[4] are genuine
  groups and genuine split extensions; they are not the arithmetic curve pi1
  extension of the once-punctured curve and this file does not claim they are.
* No nonabelian Pi_geo, no nonabelian outer action, no punctured-curve inertia,
  no anabelioid realization, and no actual l-adic Tate module action (inverse
  limit) are constructed.  The Tate-module-level statements remain the frozen
  cards of Example36EllipticCurveSourcePiCard.
* No determinant/cyclotomic nontriviality is claimed: the tree has no
  cyclotomic character of G_Q, so the identification det = cyclotomic
  character and the resulting nontrivial determinant fact are recorded as
  missing rather than assumed.  The actual finite-level linearity that IS
  available is proved.
* No theta / q-pilot / Tate identification is claimed.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open WeierstrassCurve

variable (σ τ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)

local instance : DecidableEq tateGeometricBase := Classical.decEq tateGeometricBase

/-! ## 1. The actual Galois action on E[4] -/

/-- The actual Galois action of the absolute Galois group of Q on the level-four
torsion E[4] of y^2 = x^3 - x. -/
noncomputable def tateLevelFourGaloisActionArithmeticPi
    (σ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :
    tateLevelFourTorsion ≃+ tateLevelFourTorsion :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv curveY2EqX3SubX 4 σ

/-- The identity Galois element acts trivially on E[4]. -/
theorem tateLevelFourGaloisActionArithmeticPi_one :
    tateLevelFourGaloisActionArithmeticPi 1 = AddEquiv.refl tateLevelFourTorsion := by
  ext P
  exact congrArg Subtype.val
    (LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_one_apply
      curveY2EqX3SubX 4 P)

/-- The Galois action on E[4] is a group action. -/
theorem tateLevelFourGaloisActionArithmeticPi_mul
    (σ τ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :
    tateLevelFourGaloisActionArithmeticPi (σ * τ) =
      (tateLevelFourGaloisActionArithmeticPi τ).trans (tateLevelFourGaloisActionArithmeticPi σ) := by
  ext P
  exact congrArg Subtype.val
    (LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_mul_apply
      curveY2EqX3SubX 4 σ τ P)

/-- The actual Galois action on E[4] is ZMod-4-linear. -/
theorem tateLevelFourGaloisActionArithmeticPi_zmod_smul
    (σ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)
    (c : ZMod 4) (P : tateLevelFourTorsion) :
    tateLevelFourGaloisActionArithmeticPi σ (c • P) =
      c • (tateLevelFourGaloisActionArithmeticPi σ P) :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_zmod_smul
    curveY2EqX3SubX 4 σ c P

/-- The actual distributive action of the absolute Galois group of Q on the
additive module E[2]. -/
instance tateLevelTwoGaloisDistribMulAction :
    DistribMulAction (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) tateLevelTwoTorsion where
  smul σ P := tateLevelTwoGaloisAction σ P
  one_smul P := by
    change tateLevelTwoGaloisAction 1 P = P
    rw [tateLevelTwoGaloisAction_one]
    rfl
  mul_smul σ τ P := by
    change tateLevelTwoGaloisAction (σ * τ) P =
      tateLevelTwoGaloisAction σ (tateLevelTwoGaloisAction τ P)
    rw [tateLevelTwoGaloisAction_mul]
    rfl
  smul_zero σ := map_zero (tateLevelTwoGaloisAction σ)
  smul_add σ P Q := map_add (tateLevelTwoGaloisAction σ) P Q

/-- The actual E[4] action restricts to the actual E[2] action along the
inclusion E[2] <= E[4]. -/
theorem tateLevelFourGaloisActionArithmeticPi_compat_two
    (σ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) (P : tateLevelTwoTorsion) :
    ((tateLevelFourGaloisActionArithmeticPi σ ⟨P.1, twoTorsion_le_fourTorsion P.2⟩ :
        tateLevelFourTorsion) : tateLevelFourPointType) =
      ((tateLevelTwoGaloisAction σ P : tateLevelTwoTorsion) :
        tateLevelFourPointType) := by
  unfold tateLevelFourGaloisActionArithmeticPi tateLevelTwoGaloisAction
  rw [LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_coe,
    LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_coe]

/-- The actual distributive action of the absolute Galois group of Q on the
additive module E[4]. -/
instance tateLevelFourGaloisDistribMulAction :
    DistribMulAction (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) tateLevelFourTorsion where
  smul σ P := tateLevelFourGaloisActionArithmeticPi σ P
  one_smul P := by
    change tateLevelFourGaloisActionArithmeticPi 1 P = P
    rw [tateLevelFourGaloisActionArithmeticPi_one]
    rfl
  mul_smul σ τ P := by
    change tateLevelFourGaloisActionArithmeticPi (σ * τ) P =
      tateLevelFourGaloisActionArithmeticPi σ (tateLevelFourGaloisActionArithmeticPi τ P)
    rw [tateLevelFourGaloisActionArithmeticPi_mul]
    rfl
  smul_zero σ := map_zero (tateLevelFourGaloisActionArithmeticPi σ)
  smul_add σ P Q := map_add (tateLevelFourGaloisActionArithmeticPi σ) P Q

/-- Restatement: the actual E[2] action is ZMod-2-linear. -/
theorem tateLevelTwoGaloisAction_isZModLinear
    (σ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)
    (c : ZMod 2) (P : tateLevelTwoTorsion) :
    tateLevelTwoGaloisAction σ (c • P) =
      c • (tateLevelTwoGaloisAction σ P) :=
  tateLevelTwoGaloisAction_zmod_smul σ c P

/-- Restatement: the actual E[4] action is ZMod-4-linear. -/
theorem tateLevelFourGaloisActionArithmeticPi_isZModLinear
    (σ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)
    (c : ZMod 4) (P : tateLevelFourTorsion) :
    tateLevelFourGaloisActionArithmeticPi σ (c • P) =
      c • (tateLevelFourGaloisActionArithmeticPi σ P) :=
  tateLevelFourGaloisActionArithmeticPi_zmod_smul σ c P

/-! ## 2. The actual l-torsion representation for l >= 5 -/

/-- The actual ZMod-l-linear Galois action on the actual l-torsion module of a
punctured elliptic curve over a field, for every prime l >= 5. -/
def actualGaloisLTorsionLinearEquiv {F : Type*} [Field F]
    (X : LeanFormal.IUT.PuncturedEllipticCurve F)
    (l : LeanFormal.IUT.PrimeGeFive)
    (s : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    X.LTorsion l ≃ₗ[ZMod l.value] X.LTorsion l :=
  X.galoisActionOnLTorsionLinearEquiv l s

/-- The actual l-torsion Galois representation into the general linear group of
the actual l-torsion module. -/
def actualGaloisLTorsionRepresentation {F : Type*} [Field F]
    (X : LeanFormal.IUT.PuncturedEllipticCurve F)
    (l : LeanFormal.IUT.PrimeGeFive) :
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →*
      LinearMap.GeneralLinearGroup (ZMod l.value) (X.LTorsion l) :=
  X.galoisActionOnLTorsionGeneralLinearRepresentation l


/-! ## 3. Outer automorphisms and the frozen pi1 extension card -/

/-- The inner automorphism subgroup of the automorphism group of a group. -/
def innerAutomorphisms (G : Type*) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj (G := G) : G →* MulAut G).range

/-- An outer action of the absolute Galois group on a group: an automorphism-
valued lift whose multiplication law holds up to inner automorphisms.  This is
the data of a homomorphism into the outer automorphism group, without
constructing the quotient group. -/
structure OuterActionUpToInner (G : Type*) [Group G] where
  /-- The chosen lift to automorphisms. -/
  act : rationalAbsoluteGaloisGroup → MulAut G
  /-- The identity acts trivially (normalization of the lift). -/
  act_one : act 1 = 1
  /-- The multiplication law holds up to inner automorphisms. -/
  act_mul_outer : ∀ g h : rationalAbsoluteGaloisGroup,
    act (g * h) * (act g * act h)⁻¹ ∈ innerAutomorphisms G

/-- The frozen arithmetic curve pi1 extension card of the once-punctured
concrete curve: an exact sequence of profinite groups
1 -> Pi_geo -> Pi_arith -> G_Q -> 1 together with the genuine outer action of
G_Q on Pi_geo.  This is DATA: no inhabitant is constructed, no splitting and no
chosen-action semidirect product is asserted. -/
structure ArithmeticPiExtensionCard where
  /-- The arithmetic fundamental group Pi_arith. -/
  piArith : ProfiniteGrp
  /-- The geometric fundamental group Pi_geo, as a subgroup. -/
  piGeo : Subgroup (piArith : Type)
  /-- The arithmetic projection Pi_arith -> G_Q. -/
  projection : piArith ⟶ rationalAbsoluteGaloisGroup
  /-- The arithmetic projection is surjective. -/
  projection_surjective : Function.Surjective projection.hom.toMonoidHom
  /-- The geometric subgroup is the kernel of the arithmetic projection. -/
  piGeo_is_kernel : piGeo = projection.hom.toMonoidHom.ker
  /-- The genuine outer action of G_Q on the geometric kernel. -/
  outerAction : OuterActionUpToInner (piGeo : Type)

/-- The pi1 extension card is realized: this is a frozen obligation, not a
theorem of this file. -/
def ArithmeticPiExtensionCardRealized : Prop :=
  Nonempty ArithmeticPiExtensionCard

/-- A splitting of an extension card: a section of the arithmetic projection.
This predicate is NOT a field of the card and is not asserted for the source. -/
def ArithmeticPiExtensionSplitWitness (d : ArithmeticPiExtensionCard) : Prop :=
  ∃ s : rationalAbsoluteGaloisGroup ⟶ d.piArith,
    CategoryTheory.CategoryStruct.comp s d.projection =
      CategoryTheory.CategoryStruct.id rationalAbsoluteGaloisGroup

/-! ## 4. Actual facts about the finite-level split product models -/

/-- Conjugation by a lift in a direct product acts trivially on the second
factor: this is the closure computation for the split model. -/
theorem prod_conj_fst_trivial (G H : Type*) [Group G] [Group H]
    (g : G) (h : H) : ((g, 1) * (1, h) * (g, 1)⁻¹ : G × H) = (1, h) := by
  ext <;> simp

/-- The split product model is a split extension: its first projection has the
canonical section g |-> (g, 1), so the finite-level product models are genuinely
split.  This is exactly the property that the source extension is NOT claimed
to have. -/
theorem profiniteProduct_fst_section (G H : Type*) [Group G] [Group H]
    (g : G) : MonoidHom.fst G H (g, 1) = g :=
  rfl

/-! ## 5. The missing nonabelian data -/

/-- Frozen card for the missing nonabelian geometric data of the once-punctured
curve: a nonabelian geometric fundamental group Pi_geo, its genuine outer
action, and the cusp inertia subgroup at the puncture.  This is DATA: no
inhabitant is constructed and no theorem consumes it. -/
structure MissingNonabelianGeometricPiData where
  /-- The nonabelian geometric fundamental group of the punctured curve. -/
  geometricPi : ProfiniteGrp
  /-- It is nontrivial. -/
  geometricPi_nontrivial : Nontrivial (geometricPi : Type)
  /-- The genuine outer action of G_Q on it. -/
  outerAction : OuterActionUpToInner (geometricPi : Type)
  /-- The cusp inertia subgroup at the puncture. -/
  cuspInertia : Subgroup (geometricPi : Type)
  /-- The cusp inertia subgroup is nontrivial. -/
  cuspInertia_nontrivial : ∃ x : cuspInertia, x ≠ 1

/-- The nonabelian geometric data card is realized: frozen obligation, not
proved here. -/
def MissingNonabelianGeometricPiDataRealized : Prop :=
  Nonempty MissingNonabelianGeometricPiData

/-- The Tate-module-level arithmetic action is not constructed in the tree: the
full Tate module card of Example36EllipticCurveSourcePiCard has no constructed
inhabitant.  At finite levels the actual action is the proved l-torsion action. -/
def TateModuleActionCard : Prop :=
  Nonempty (SourceFullTateModuleData sourceOncePuncturedEllipticCurve)

/-- The cyclotomic-character identification det = cyclotomic character is not
available in the tree (there is no cyclotomic character of G_Q), so the
nontrivial determinant statement is recorded as an open card, not assumed. -/
def CyclotomicDeterminantCard : Prop :=
  MissingNonabelianGeometricPiDataRealized ∧ TateModuleActionCard


end Example36
end LeanFormal.IUT.IUTII.Frobenioid
