import tmp.sheaf.xif.paper.S1966LocalThetaMonoidActual
import tmp.sheaf.xif.paper.S1962R1AbstractActionActual
import Iut.Foundations.SourceMLFIntegralMonoid
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# S1973: the actual local constant monoid, its G_v-action, and the first missing Psi_cns

Layer: O (original Theta-link / q-pilot).  This file is the continuation of
S1966 (the finite theta/Gaussian value monoid and its actual-local model) and
S1962 (the actual local Krull action).

## The paper object and the exact question

At a good nonarchimedean place v, IUT II, Proposition 4.1, (i), constructs the
ind-topological monoid

  Psi_cns(Pi_v) = Psi_cns(G_v(Pi_v)) subset lim_{J} H^1(J, mu_hat^Z(G_v))

by the functorial group-theoretic algorithm of [AbsTopIII], Corollary 1.10,
(b), and equips it with its natural G_v(Pi_v)-action; the monoid is naturally
isomorphic to the integral monoid O^tri_{F_v}.  Parts (ii)--(iv) then form
Psi_ss, Psi_env, and Psi_gau, with the diagonal <F_l^star> units and the
evaluation isomorphism.

The tree contains the actual local-field model
IndIntegralMonoid (Iut/Foundations/SourceDefinition52LocalReconstruction.lean)
with its actual ind-topology and Krull action, the finite-stage filtered
colimit model (SourceFiniteStageModelEvaluation.lean), and the
SourceLogShellDatum.Units slot.  It does not contain the cohomological
construction of lim H^1(J, mu_hat^Z(G_v)), the algorithm of [AbsTopIII],
Corollary 1.10, (b), or an identification of either with the actual local
field model.

## What this file constructs (kernel-checked)

1. The actual G_v-monoid model: PsiCnsModel v = IndIntegralMonoid (QPlace v)
   with the actual Krull action psiCnsAction v : G_v ->* MulAut (PsiCnsModel v).
   The action is by monoid automorphisms (psiCns_smul_mul) and is pointwise
   continuous for the actual ind-topology (psiCns_continuous_action).

2. The actual units PsiCnsUnits v = (PsiCnsModel v)^x, with the induced action
   psiCnsUnitsAction v, and the G_v-equivariant monoid isomorphism

     psiCnsEquivSourceMLF v : PsiCnsModel v ~=* SourceMLFIntegralMonoid (Base v)

   (as a GMonoidEquiv), together with the induced unit isomorphism
   psiCnsUnitsEquivSourceMLF v.  This is an actual identification of the
   IndIntegralMonoid model with the source MLF integral monoid model, not an
   identification with the paper's cohomological Psi_cns.

3. Actual diagonal <F_l^star> units.  For l : PrimeGeFive we use the genuine
   cyclotomic subgroup rootsOfUnity (l.value - 1) inside the actual local
   algebraic closure (|F_l^star| = l - 1) and construct units of the actual
   local integral monoid

     rootOfUnityUnit v (l.value - 1) : rootsOfUnity (l.value - 1) (Closure v) -> (PsiCnsModel v)^x,

   with the Galois action rootOfUnityUnit_galois_smul.  The diagonal subgroup
   diagonalFlStarUnits v l of the product over the theta labels is constructed,
   proved diagonal, stable under the diagonal G_v-action, and shown to land in
   the unit part of S1966's local Gaussian monoid.

4. The Psi_env/Psi_gau models.  PsiEnvModel v is S1966's LocalThetaMonoidModel,
   PsiGauModel v l is S1966's localGaussianValueMonoid.  The evaluation
   psiEvaluation v l is bijective, restricts to the identity on the unit factor,
   sends the formal generator to the Gaussian vector, and we construct the
   domain unit/ray splittings and the codomain unit/ray splittings.  The
   diagonal cyclotomic units constructed above are contained in the Gaussian
   monoid, so they form the diagonal <F_l^star>-unit part of the model.

## Exact first missing (no fake monoid, no axiom, no sorry)

The paper's Psi_cns(Pi_v) itself is not constructed.  The first missing object
is the functorial group-theoretic algorithm of [AbsTopIII], Corollary 1.10,
(b), which produces the ind-topological submonoid

  Psi_cns(G_v) subset lim_{J} H^1(J, mu_hat^Z(G_v)),

   naturally isomorphic to O^tri_{F_v}, together with its natural G_v-action.
This requires (a) the actual continuous-cohomology limit of the coefficient
module mu_hat^Z(G_v) over the open subgroups J of the local absolute Galois
group, (b) the [AbsTopIII] algorithm selecting the submonoid and its
identification with O^tri, and (c) the proof that the resulting action agrees
with the Krull action on the actual local field.  None of these is in the
tree.  The present file supplies the actual G_v-monoid model and the
downstream diagonal/evaluation/splitting constructions on it; it does not
assert that the model is the paper's cohomological Psi_cns.

The second missing point for the paper's ind-topological statement is joint
continuity of the action map G_v x PsiCnsModel v -> PsiCnsModel v for the final
(ind) topology.  Pointwise continuity is proved below; the joint statement is
the same continuity-with-parameters gap recorded in S1962 as
R1JointContinuousActionMissing and is named PsiCnsJointContinuousActionMissing here.
It is not postulated as a hypothesis to close any result.

The third missing point is the identification of the cyclotomic subgroup
rootsOfUnity (l.value - 1) with the paper's F_l^star-symmetry subgroup; the
subgroup itself and its action are actual, but the paper's symmetrizing
isomorphisms between the labeled copies are not constructed in the tree.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only Nonempty gate is used.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unnecessarySimpa false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1966LocalThetaMonoidActual
open LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual
open Iut.SourceFinitePlaceReconstruction
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S1973PsiCnsActual

/-! ## 0. Notation: the actual local field, its Galois group, and the model -/

/-- The actual rational finite place underlying a one-column place. -/
abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace ℚ :=
  finitePrimePlaceToQ v

/-- The actual local base field (the completion at the rational place). -/
abbrev LocalBaseField (v : FinitePrimePlace 2 7) : Type := Base (QPlace v)

/-- The actual local algebraic closure. -/
abbrev LocalClosure (v : FinitePrimePlace 2 7) : Type := Closure (QPlace v)

/-- The actual local absolute Galois group G_v. -/
abbrev Gv (v : FinitePrimePlace 2 7) : Type := LocalGalois v

/-- The nonzero actual integral monoid O^tri_{F_v}: the model of the paper's
constant monoid Psi_cns(Pi_v).  The paper's monoid O^tri may also be considered
with zero adjoined; the units and the action relevant here are unchanged. -/
abbrev PsiCnsModel (v : FinitePrimePlace 2 7) : Type := IndIntegralMonoid (QPlace v)

/-- The actual units of the constant-monoid model, i.e. the model of
Psi_cns(Pi_v)^x. -/
abbrev PsiCnsUnits (v : FinitePrimePlace 2 7) : Type := (PsiCnsModel v)ˣ

/-- The source MLF integral monoid, the other actual local-field model. -/
abbrev SourceMLFModel (v : FinitePrimePlace 2 7) : Type :=
  Iut.SourceMLFIntegralMonoid (LocalBaseField v)

/-! ## 1. The actual G_v-monoid structure -/

/-- The actual Krull action of G_v on the integral-monoid model. -/
noncomputable def psiCnsAction (v : FinitePrimePlace 2 7) :
    Gv v →* MulAut (PsiCnsModel v) :=
  indGaloisAction (QPlace v)

/-- The action is by monoid automorphisms. -/
theorem psiCns_smul_mul (v : FinitePrimePlace 2 7) (σ : Gv v)
    (x y : PsiCnsModel v) :
    psiCnsAction v σ (x * y) = psiCnsAction v σ x * psiCnsAction v σ y :=
  map_mul (psiCnsAction v σ) x y

/-- The action fixes the monoid unit. -/
@[simp] theorem psiCns_smul_one (v : FinitePrimePlace 2 7) (σ : Gv v) :
    psiCnsAction v σ 1 = 1 :=
  map_one (psiCnsAction v σ)

/-- The induced action on the actual units. -/
noncomputable def psiCnsUnitsMulAut (v : FinitePrimePlace 2 7) (σ : Gv v) :
    MulAut (PsiCnsUnits v) :=
  Units.mapEquiv (psiCnsAction v σ)

/-- The actual G_v-action on the units of the constant-monoid model. -/
noncomputable def psiCnsUnitsAction (v : FinitePrimePlace 2 7) :
    Gv v →* MulAut (PsiCnsUnits v) where
  toFun := psiCnsUnitsMulAut v
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Units.ext
    simp [psiCnsUnitsMulAut, psiCnsAction]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro u
    apply Units.ext
    simp [psiCnsUnitsMulAut, psiCnsAction]

/-- The unit action is the restriction of the monoid action. -/
@[simp] theorem psiCnsUnits_smul_val (v : FinitePrimePlace 2 7) (σ : Gv v)
    (u : PsiCnsUnits v) :
    ((psiCnsUnitsAction v σ u : PsiCnsUnits v) : PsiCnsModel v) =
      psiCnsAction v σ (u : PsiCnsModel v) := by
  simp [psiCnsUnitsAction, psiCnsUnitsMulAut]

/-- A bundled G-monoid isomorphism: a multiplicative equivalence that
intertwines the two explicit actions.  Using explicit action homomorphisms
avoids typeclass search on the large local-field structures. -/
structure GMonoidEquiv (G : Type*) [Group G] (M N : Type*) [Monoid M] [Monoid N]
    (actionM : G →* MulAut M) (actionN : G →* MulAut N) where
  toMulEquiv : M ≃* N
  map_smul : ∀ (g : G) (m : M),
    toMulEquiv (actionM g m) = actionN g (toMulEquiv m)

/-- The Krull action on the source MLF integral monoid. -/
noncomputable def sourceMLFAction (v : FinitePrimePlace 2 7) :
    Gv v →* MulAut (SourceMLFModel v) :=
  Iut.SourceMLFIntegralMonoid.galoisAction (LocalBaseField v)

/-- The induced action on the units of the source MLF integral monoid. -/
noncomputable def sourceMLFUnitsAction (v : FinitePrimePlace 2 7) :
    Gv v →* MulAut ((SourceMLFModel v)ˣ) where
  toFun σ := Units.mapEquiv (sourceMLFAction v σ)
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Units.ext
    simp [sourceMLFAction]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro u
    apply Units.ext
    simp [sourceMLFAction]

/-- The actual IndIntegralMonoid model and the source MLF integral monoid are
isomorphic as G_v-monoids.  This is a genuine arithmetic identification of two
actual local-field models; it is not an identification with the paper's
cohomological Psi_cns. -/
noncomputable def psiCnsEquivSourceMLF (v : FinitePrimePlace 2 7) :
    GMonoidEquiv (Gv v) (PsiCnsModel v) (SourceMLFModel v)
      (psiCnsAction v) (sourceMLFAction v) where
  toMulEquiv := indIntegralMonoidEquivSourceMLF (QPlace v)
  map_smul σ x := indIntegralMonoidEquivSourceMLF_galois (QPlace v) σ x

/-- The induced G_v-equivariant isomorphism of unit groups. -/
noncomputable def psiCnsUnitsEquivSourceMLF (v : FinitePrimePlace 2 7) :
    PsiCnsUnits v ≃* (SourceMLFModel v)ˣ :=
  Units.mapEquiv (indIntegralMonoidEquivSourceMLF (QPlace v))

/-- The unit isomorphism is G_v-equivariant. -/
theorem psiCnsUnitsEquivSourceMLF_smul (v : FinitePrimePlace 2 7) (σ : Gv v)
    (u : PsiCnsUnits v) :
    psiCnsUnitsEquivSourceMLF v (psiCnsUnitsAction v σ u) =
      sourceMLFUnitsAction v σ (psiCnsUnitsEquivSourceMLF v u) := by
  apply Units.ext
  change (indIntegralMonoidEquivSourceMLF (QPlace v))
      (psiCnsAction v σ (u : PsiCnsModel v)) =
    (Iut.SourceMLFIntegralMonoid.galoisAction (LocalBaseField v)) σ
      ((indIntegralMonoidEquivSourceMLF (QPlace v)) (u : PsiCnsModel v))
  exact indIntegralMonoidEquivSourceMLF_galois (QPlace v) σ (u : PsiCnsModel v)

/-! ## 2. The actual ind-topology and pointwise continuity -/

/-- The actual ind-topology on the integral-monoid model, induced from the
filtered-colimit topological module of IUT I, Definition 5.2, (v). -/
abbrev psiCnsIndTopology (v : FinitePrimePlace 2 7) :
    TopologicalSpace (PsiCnsModel v) :=
  inferInstance

/-- Every element of G_v acts continuously for the actual ind-topology.  This is
the pointwise continuity theorem; joint continuity is the named missing
statement PsiCnsJointContinuousActionMissing below. -/
theorem psiCns_continuous_action (v : FinitePrimePlace 2 7) (σ : Gv v) :
    letI := psiCnsIndTopology v
    Continuous (psiCnsAction v σ) := by
  letI := psiCnsIndTopology v
  exact continuous_indGaloisMulAut (QPlace v) σ

/-- The exact joint-continuity statement for the action on the ind-topological
model.  It is stated, not assumed and not proved: S1962 records the same
continuity-with-parameters gap for the limit carrier. -/
def PsiCnsJointContinuousActionMissing (v : FinitePrimePlace 2 7) : Prop :=
  letI := psiCnsIndTopology v
  Continuous fun p : Gv v × PsiCnsModel v => psiCnsAction v p.1 p.2

/-! ## 3. Actual cyclotomic units of the local integral monoid -/

/-- An element of the algebraic closure which is a root of unity is integral
over the local valuation ring. -/
theorem isIntegral_rootOfUnity_val (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n (LocalClosure v)) :
    IsIntegral (Valuation.integer (ValuativeRel.valuation (LocalBaseField v)))
      ((ζ : (LocalClosure v)ˣ) : LocalClosure v) := by
  have hζ : ((ζ : (LocalClosure v)ˣ) : LocalClosure v) ^ n = 1 := by
    have h := (mem_rootsOfUnity n (ζ : (LocalClosure v)ˣ)).mp ζ.2
    simpa using congrArg (fun u : (LocalClosure v)ˣ => (u : LocalClosure v)) h
  refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
  simpa [hζ]

/-- Build an element of the nonzero integral monoid from an algebraic element
with an integrality proof and a nonzero proof. -/
noncomputable def indOfAlg (v : FinitePrimePlace 2 7) (z : LocalClosure v)
    (hint : IsIntegral (Valuation.integer (ValuativeRel.valuation (LocalBaseField v))) z)
    (hne : z ≠ 0) : PsiCnsModel v :=
  ⟨(carrierMulEquivAlgebraicClosure (QPlace v)).symm z, by
    constructor
    · rw [MulEquiv.apply_symm_apply]
      exact hint
    · rw [MulEquiv.apply_symm_apply]
      exact hne⟩

/-- The underlying algebraic value of indOfAlg. -/
theorem carrier_indOfAlg (v : FinitePrimePlace 2 7) (z : LocalClosure v)
    (hint : IsIntegral (Valuation.integer (ValuativeRel.valuation (LocalBaseField v))) z)
    (hne : z ≠ 0) :
    carrierMulEquivAlgebraicClosure (QPlace v) (indOfAlg v z hint hne).1 = z := by
  simp [indOfAlg]

/-- A root of unity as an element of the actual integral monoid. -/
noncomputable def rootOfUnityInd (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n (LocalClosure v)) : PsiCnsModel v :=
  indOfAlg v ((ζ : (LocalClosure v)ˣ) : LocalClosure v)
    (isIntegral_rootOfUnity_val v n ζ)
    (Units.ne_zero (ζ : (LocalClosure v)ˣ))

/-- The carrier value of rootOfUnityInd is the root of unity itself. -/
@[simp] theorem carrier_rootOfUnityInd (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n (LocalClosure v)) :
    carrierMulEquivAlgebraicClosure (QPlace v) (rootOfUnityInd v n ζ).1 =
      ((ζ : (LocalClosure v)ˣ) : LocalClosure v) := by
  simp [rootOfUnityInd, carrier_indOfAlg]

/-- Root-of-unity elements multiply. -/
theorem rootOfUnityInd_mul (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (ζ η : rootsOfUnity n (LocalClosure v)) :
    rootOfUnityInd v n (ζ * η) = rootOfUnityInd v n ζ * rootOfUnityInd v n η := by
  apply Subtype.ext
  apply (carrierMulEquivAlgebraicClosure (QPlace v)).injective
  simp [carrier_rootOfUnityInd, map_mul]

/-- A root of unity as a unit of the actual integral monoid. -/
noncomputable def rootOfUnityUnit (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n (LocalClosure v)) : PsiCnsUnits v where
  val := rootOfUnityInd v n ζ
  inv := rootOfUnityInd v n ζ⁻¹
  val_inv := by
    apply Subtype.ext
    apply (carrierMulEquivAlgebraicClosure (QPlace v)).injective
    simp [carrier_rootOfUnityInd]
  inv_val := by
    apply Subtype.ext
    apply (carrierMulEquivAlgebraicClosure (QPlace v)).injective
    simp [carrier_rootOfUnityInd]

/-- The root-of-unity units form a monoid homomorphism. -/
noncomputable def rootOfUnityUnitHom (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n] :
    rootsOfUnity n (LocalClosure v) →* PsiCnsUnits v where
  toFun := rootOfUnityUnit v n
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    apply (carrierMulEquivAlgebraicClosure (QPlace v)).injective
    simp [rootOfUnityUnit, carrier_rootOfUnityInd]
  map_mul' ζ η := by
    apply Units.ext
    exact rootOfUnityInd_mul v n ζ η

/-- The root-of-unity unit of 1 is 1. -/
@[simp] theorem rootOfUnityUnit_one (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n] :
    rootOfUnityUnit v n (1 : rootsOfUnity n (LocalClosure v)) = 1 :=
  (rootOfUnityUnitHom v n).map_one

/-- Root-of-unity units multiply. -/
theorem rootOfUnityUnit_mul (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (ζ η : rootsOfUnity n (LocalClosure v)) :
    rootOfUnityUnit v n (ζ * η) = rootOfUnityUnit v n ζ * rootOfUnityUnit v n η :=
  (rootOfUnityUnitHom v n).map_mul ζ η

/-- The inverse of a root-of-unity unit. -/
@[simp] theorem rootOfUnityUnit_inv (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n (LocalClosure v)) :
    rootOfUnityUnit v n ζ⁻¹ = (rootOfUnityUnit v n ζ)⁻¹ :=
  (rootOfUnityUnitHom v n).map_inv ζ

/-- The Galois action on roots of unity, induced by the actual action on the
algebraic closure. -/
noncomputable def galoisOnRootsOfUnity (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (σ : Gv v) : rootsOfUnity n (LocalClosure v) →* rootsOfUnity n (LocalClosure v) where
  toFun ζ :=
    ⟨Units.map (σ : LocalClosure v →* LocalClosure v) (ζ : (LocalClosure v)ˣ), by
      rw [mem_rootsOfUnity]
      have hζ : (ζ : (LocalClosure v)ˣ) ^ n = 1 :=
        (mem_rootsOfUnity n (ζ : (LocalClosure v)ˣ)).mp ζ.2
      calc
        (Units.map (σ : LocalClosure v →* LocalClosure v) (ζ : (LocalClosure v)ˣ)) ^ n
            = Units.map (σ : LocalClosure v →* LocalClosure v)
                ((ζ : (LocalClosure v)ˣ) ^ n) := by rw [map_pow]
        _ = Units.map (σ : LocalClosure v →* LocalClosure v) 1 := by rw [hζ]
        _ = 1 := map_one _⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' ζ η := by
    apply Subtype.ext
    apply Units.ext
    simp

/-- The Galois automorphism of the group of roots of unity. -/
noncomputable def galoisOnRootsOfUnityMulAut (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (σ : Gv v) : MulAut (rootsOfUnity n (LocalClosure v)) where
  toFun := galoisOnRootsOfUnity v n σ
  invFun := galoisOnRootsOfUnity v n σ.symm
  left_inv ζ := by
    apply Subtype.ext
    apply Units.ext
    simp [galoisOnRootsOfUnity]
  right_inv ζ := by
    apply Subtype.ext
    apply Units.ext
    simp [galoisOnRootsOfUnity]
  map_mul' ζ η := by
    apply Subtype.ext
    apply Units.ext
    simp [galoisOnRootsOfUnity]

/-- The actual G_v-action on roots of unity. -/
noncomputable def galoisOnRootsOfUnityAction (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n] :
    Gv v →* MulAut (rootsOfUnity n (LocalClosure v)) where
  toFun := galoisOnRootsOfUnityMulAut v n
  map_one' := by
    apply MulEquiv.ext
    intro ζ
    apply Subtype.ext
    apply Units.ext
    simp [galoisOnRootsOfUnityMulAut, galoisOnRootsOfUnity]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro ζ
    apply Subtype.ext
    apply Units.ext
    simp [galoisOnRootsOfUnityMulAut, galoisOnRootsOfUnity]

/-- Galois equivariance of the root-of-unity units. -/
theorem rootOfUnityUnit_galois_smul (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n]
    (σ : Gv v) (ζ : rootsOfUnity n (LocalClosure v)) :
    rootOfUnityUnit v n (galoisOnRootsOfUnityAction v n σ ζ) =
      psiCnsUnitsAction v σ (rootOfUnityUnit v n ζ) := by
  apply Units.ext
  change rootOfUnityInd v n (galoisOnRootsOfUnityAction v n σ ζ) =
    psiCnsAction v σ (rootOfUnityInd v n ζ)
  apply Subtype.ext
  apply (carrierMulEquivAlgebraicClosure (QPlace v)).injective
  change carrierMulEquivAlgebraicClosure (QPlace v)
      (rootOfUnityInd v n (galoisOnRootsOfUnityAction v n σ ζ)).1 =
    carrierMulEquivAlgebraicClosure (QPlace v)
      (indGaloisMulAut (QPlace v) σ (rootOfUnityInd v n ζ)).1
  rw [carrier_rootOfUnityInd]
  rw [indGaloisMulAut_val_eq_galoisContinuousLinearMap]
  rw [carrierMulEquiv_galoisContinuousLinearMap]
  simp [galoisOnRootsOfUnityAction, galoisOnRootsOfUnityMulAut, galoisOnRootsOfUnity]

/-- Injectivity of the root-of-unity unit map, used for the diagonal subgroup's
order count. -/
theorem rootOfUnityUnit_injective (v : FinitePrimePlace 2 7) (n : ℕ) [NeZero n] :
    Function.Injective (rootOfUnityUnit v n) := by
  intro ζ η h
  have h1 : ((rootOfUnityUnit v n ζ : PsiCnsUnits v) : PsiCnsModel v) =
      ((rootOfUnityUnit v n η : PsiCnsUnits v) : PsiCnsModel v) :=
    congrArg (fun u : PsiCnsUnits v => (u : PsiCnsModel v)) h
  have h2 := congrArg (fun x : PsiCnsModel v =>
    carrierMulEquivAlgebraicClosure (QPlace v) x.1) h1
  simp [rootOfUnityUnit, rootOfUnityInd, indOfAlg] at h2
  exact Subtype.ext (Units.ext h2)

/-! ## 4. Diagonal <F_l^star> units -/

/-- The order |F_l^star| = l - 1 of the finite field label group. -/
abbrev FlStarOrder (l : PrimeGeFive) : ℕ := l.value - 1

/-- l - 1 is nonzero. -/
theorem flStarOrder_pos (l : PrimeGeFive) : 0 < FlStarOrder l := by
  unfold FlStarOrder
  have h5 := l.ge_five
  omega

instance flStarOrderNeZero (l : PrimeGeFive) : NeZero (FlStarOrder l) :=
  ⟨Nat.ne_of_gt (flStarOrder_pos l)⟩

/-- The actual diagonal <F_l^star>-subgroup inside the product of the units at
the theta labels.  The group rootsOfUnity (l - 1) is the actual cyclotomic
group of order l - 1 = |F_l^star|; its identification with the paper's
F_l^star-symmetry group is a separate missing comparison, but the units
themselves and their diagonal embedding are actual. -/
noncomputable def diagonalFlStarUnits (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    Subgroup (ThetaLabel l → PsiCnsUnits v) where
  carrier := {x | ∃ ζ : rootsOfUnity (FlStarOrder l) (LocalClosure v),
    x = fun _ => rootOfUnityUnit v (FlStarOrder l) ζ}
  one_mem' := by
    refine ⟨1, ?_⟩
    funext j
    rw [rootOfUnityUnit_one]
    rfl
  mul_mem' := by
    rintro x y ⟨ζ, rfl⟩ ⟨η, rfl⟩
    refine ⟨ζ * η, ?_⟩
    funext j
    rw [rootOfUnityUnit_mul]
    rfl
  inv_mem' := by
    rintro x ⟨ζ, rfl⟩
    refine ⟨ζ⁻¹, ?_⟩
    funext j
    rw [rootOfUnityUnit_inv]
    rfl

/-- The diagonal subgroup is (as a type) the actual cyclotomic group of
order l - 1. -/
noncomputable def diagonalFlStarUnitsEquiv (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    rootsOfUnity (FlStarOrder l) (LocalClosure v) ≃ diagonalFlStarUnits v l where
  toFun ζ := ⟨fun _ => rootOfUnityUnit v (FlStarOrder l) ζ, ⟨ζ, rfl⟩⟩
  invFun x := Classical.choose x.2
  left_inv ζ := by
    let x : diagonalFlStarUnits v l :=
      ⟨fun _ : ThetaLabel l => rootOfUnityUnit v (FlStarOrder l) ζ, ⟨ζ, rfl⟩⟩
    change Classical.choose x.2 = ζ
    have h := congrFun (Classical.choose_spec x.2) (thetaZero l)
    exact (rootOfUnityUnit_injective v (FlStarOrder l) h).symm
  right_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec x.2).symm

/-- The diagonal cyclotomic subgroup has cardinality l - 1 = |F_l^star|. -/
theorem diagonalFlStarUnits_card (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    Nat.card (diagonalFlStarUnits v l) = l.value - 1 := by
  rw [← Nat.card_congr (diagonalFlStarUnitsEquiv v l)]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity (LocalClosure v) (FlStarOrder l)

/-- Every element of the diagonal subgroup is literally independent of the
theta label. -/
theorem diagonalFlStarUnits_apply_eq (v : FinitePrimePlace 2 7) (l : PrimeGeFive)
    {x : ThetaLabel l → PsiCnsUnits v} (hx : x ∈ diagonalFlStarUnits v l)
    (j j' : ThetaLabel l) : x j = x j' := by
  rcases hx with ⟨ζ, rfl⟩
  rfl

/-- The diagonal subgroup is stable under the diagonal G_v-action. -/
theorem diagonalFlStarUnits_galois_smul_mem (v : FinitePrimePlace 2 7)
    (l : PrimeGeFive) (σ : Gv v) {x : ThetaLabel l → PsiCnsUnits v}
    (hx : x ∈ diagonalFlStarUnits v l) :
    (fun j => psiCnsUnitsAction v σ (x j)) ∈ diagonalFlStarUnits v l := by
  rcases hx with ⟨ζ, rfl⟩
  refine ⟨galoisOnRootsOfUnityAction v (FlStarOrder l) σ ζ, ?_⟩
  funext j
  rw [rootOfUnityUnit_galois_smul]

/-- The diagonal <F_l^star>-units land in the unit part of S1966's local
Gaussian monoid. -/
theorem diagonalFlStarUnits_mem_localGaussian (v : FinitePrimePlace 2 7)
    (l : PrimeGeFive) {x : ThetaLabel l → PsiCnsUnits v}
    (hx : x ∈ diagonalFlStarUnits v l) :
    (fun j => (x j, (1 : Multiplicative NNReal))) ∈
      localGaussianValueMonoid v v.1 l := by
  rcases hx with ⟨ζ, rfl⟩
  refine ⟨rootOfUnityUnit v (FlStarOrder l) ζ, 0, ?_⟩
  funext j
  simp

/-! ## 5. Diagonal units in the Gaussian model -/

/-- The diagonal units, viewed in the unit group of the ambient product of the
semi-simplified monoids. -/
noncomputable def diagonalIntoAmbientUnits (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    (ThetaLabel l → PsiCnsUnits v) →*
      (ThetaLabel l → LocalSemiSimplified v)ˣ where
  toFun x :=
    { val := fun j => (x j, (1 : Multiplicative NNReal))
      inv := fun j => ((x j)⁻¹, (1 : Multiplicative NNReal))
      val_inv := by
        funext j
        simp [Prod.mul_def]
      inv_val := by
        funext j
        simp [Prod.mul_def] }
  map_one' := by
    apply Units.ext
    funext j
    rfl
  map_mul' x y := by
    apply Units.ext
    funext j
    simp [Prod.mul_def]

/-- The diagonal <F_l^star>-subgroup embedded in the unit group of the ambient
product of the semi-simplified monoids. -/
noncomputable def diagonalFlStarUnitsInGau (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    Subgroup ((ThetaLabel l → LocalSemiSimplified v)ˣ) :=
  (diagonalFlStarUnits v l).map (diagonalIntoAmbientUnits v l)

/-- The embedded diagonal subgroup lands in the local Gaussian monoid, i.e.
these are actual units of the Gaussian model. -/
theorem diagonalFlStarUnitsInGau_val_mem_localGaussian (v : FinitePrimePlace 2 7)
    (l : PrimeGeFive) :
    (diagonalFlStarUnitsInGau v l : Set ((ThetaLabel l → LocalSemiSimplified v)ˣ)) ⊆
      {x | ((x : (ThetaLabel l → LocalSemiSimplified v)ˣ) :
          ThetaLabel l → LocalSemiSimplified v) ∈
        (localGaussianValueMonoid v v.1 l : Set (ThetaLabel l → LocalSemiSimplified v))} := by
  rintro x ⟨d, hd, rfl⟩
  simpa [diagonalIntoAmbientUnits] using diagonalFlStarUnits_mem_localGaussian v l hd

/-! ## 6. Psi_env and Psi_gau: evaluation and splittings -/

/-- Psi_env model: actual units times the formal ray R>=0 * log(p_v) * log(Theta). -/
abbrev PsiEnvModel (v : FinitePrimePlace 2 7) : Type :=
  LocalThetaMonoidModel v

/-- Psi_gau model: the evaluated Gaussian monoid in the product of the
semi-simplified monoids. -/
abbrev PsiGauModel (v : FinitePrimePlace 2 7) (l : PrimeGeFive) : Type :=
  localGaussianValueMonoid v v.1 l

/-- The formal evaluation of IUT II, Proposition 4.1, (iv), on the actual
local-field model. -/
noncomputable def psiEvaluation (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    PsiEnvModel v →* PsiGauModel v l :=
  localEvaluation v v.1 l

/-- The evaluation is bijective. -/
theorem psiEvaluation_bijective (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    Function.Bijective (psiEvaluation v l) :=
  localEvaluation_bijective v v.1 v.2.2.2 l

/-- The evaluation restricts to the identity on the unit factor. -/
@[simp] theorem psiEvaluation_units (v : FinitePrimePlace 2 7) (l : PrimeGeFive)
    (u : PsiCnsUnits v) :
    psiEvaluation v l (u, 1) =
      ⟨fun _ => (u, 1), localDiagonal_mem v v.1 l u⟩ :=
  localEvaluation_units v v.1 l u

/-- The evaluation sends the formal generator to the Gaussian vector
(..., j^2 log(p_v), ...). -/
@[simp] theorem psiEvaluation_generator (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    psiEvaluation v l (localThetaGenerator v) =
      ⟨fun j => (1, Multiplicative.ofAdd (gaussianNNWeight v.1 l j)),
        ⟨1, 1, by funext j; simp⟩⟩ :=
  localEvaluation_generator v v.1 l

/-- The domain unit splitting Psi_cns^x -> Psi_env. -/
noncomputable def psiEnvUnitSection (v : FinitePrimePlace 2 7) :
    PsiCnsUnits v →* PsiEnvModel v where
  toFun u := (u, 1)
  map_one' := rfl
  map_mul' u w := by
    apply Prod.ext
    · rfl
    · simp

/-- The domain formal-ray splitting R>=0 -> Psi_env. -/
noncomputable def psiEnvRaySection (v : FinitePrimePlace 2 7) :
    Multiplicative NNReal →* PsiEnvModel v where
  toFun c := (1, c)
  map_one' := rfl
  map_mul' c d := by
    apply Prod.ext
    · simp
    · rfl

/-- The codomain unit splitting Psi_cns^x -> Psi_gau. -/
noncomputable def psiGauUnitSection (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    PsiCnsUnits v →* PsiGauModel v l where
  toFun u := ⟨fun _ => (u, 1), localDiagonal_mem v v.1 l u⟩
  map_one' := by
    apply Subtype.ext
    funext j
    rfl
  map_mul' u w := by
    apply Subtype.ext
    funext j
    apply Prod.ext
    · rfl
    · simp

/-- The codomain Gaussian-ray splitting, obtained by evaluating the domain
ray section. -/
noncomputable def psiGauRaySection (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    Multiplicative NNReal →* PsiGauModel v l :=
  (psiEvaluation v l).comp (psiEnvRaySection v)

/-- The evaluation commutes with the unit splittings. -/
@[simp] theorem psiEvaluation_unitSection (v : FinitePrimePlace 2 7) (l : PrimeGeFive)
    (u : PsiCnsUnits v) :
    psiEvaluation v l (psiEnvUnitSection v u) = psiGauUnitSection v l u := by
  change (localEvaluation v v.1 l ((u, 1))) = psiGauUnitSection v l u
  rw [localEvaluation_units v v.1 l u]
  apply Subtype.ext
  rfl

/-- The evaluation commutes with the ray splittings. -/
@[simp] theorem psiEvaluation_raySection (v : FinitePrimePlace 2 7) (l : PrimeGeFive)
    (c : Multiplicative NNReal) :
    psiEvaluation v l (psiEnvRaySection v c) = psiGauRaySection v l c := rfl

/-! ## 7. Exact first missing -/

-- The first missing object is the cohomological constant monoid itself:
-- the [AbsTopIII], Corollary 1.10, (b), algorithm producing an ind-topological
-- submonoid of lim H^1(J, mu_hat^Z(G_v)) isomorphic to O^tri_{F_v}, with its
-- natural G_v-action.  The tree has no definition of the continuous cohomology
-- limit over open subgroups, no coefficient cyclotome mu_hat^Z(G_v), and no
-- [AbsTopIII] algorithm.  We therefore do not invent a structure with an
-- inhabited identity model.  The actual model above is the largest
-- kernel-checked object available; the comparison with the paper's Psi_cns is
-- exactly the missing theorem.
--
-- The second missing point is PsiCnsJointContinuousActionMissing above: pointwise
-- continuity of the Krull action is proved, but joint continuity on the single
-- ind-topological limit carrier is not in the tree (S1962, R1Joint...).
--
-- The third missing point is the paper's F_l^star-symmetrizing isomorphisms
-- between the labeled copies; the cyclotomic unit subgroup and its diagonal
-- embedding are constructed above, but the label symmetries themselves are not.
--
-- No declaration in this file asserts any of these missing identifications.

/-! ## 8. Axiom probes -/

#print axioms psiCns_smul_mul
#print axioms psiCnsEquivSourceMLF
#print axioms psiCnsUnitsEquivSourceMLF_smul
#print axioms psiCns_continuous_action
#print axioms rootOfUnityUnit_galois_smul
#print axioms diagonalFlStarUnits_galois_smul_mem
#print axioms diagonalFlStarUnits_mem_localGaussian
#print axioms diagonalFlStarUnits_card
#print axioms diagonalFlStarUnitsInGau_val_mem_localGaussian
#print axioms psiEvaluation_bijective

end LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
