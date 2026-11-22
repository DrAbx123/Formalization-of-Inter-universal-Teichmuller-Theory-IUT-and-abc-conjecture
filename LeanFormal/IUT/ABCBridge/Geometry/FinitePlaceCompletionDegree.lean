import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Local basis degrees of finite-place completions

For an extension `k → K` of number fields and a finite place `place` of `K` above the
contracted place of `k`, this file studies the *local* basis degree
`Module.finrank k_v K_w` of the upper completion `K_w` over the lower completion
`k_v`, and relates it to the ramification index and residue degree at the place
extension.

The global-library data of the extension live at the number rings
(`Ideal.ramificationIdx'`, `Ideal.inertiaDeg'` at `(𝓞 k, v) → (𝓞 K, w)`), whereas the
fundamental identity of a finite extension of complete discretely valued fields is
stated by Mathlib at *local* rings. This file supplies the bridge that is missing in
Mathlib 4.32.2:

* `instAlgebraAdicCompletion`, `instAlgebraAdicCompletionIntegersCompletion` and
  `instAlgebraAdicCompletionIntegers` equip the upper completion `K_w` with its
  `k_v`-algebra structure and the upper completed valuation ring `𝒪_w` with its
  `𝒪_v`-algebra structure, the latter through the actual map on completed valuation
  rings. `instIsScalarTowerAdicCompletionIntegers` and
  `instIsScalarTowerAdicCompletionIntegersRing` record the two scalar towers
  `𝒪_v → k_v → K_w` and `𝒪_v → 𝒪_w → K_w` needed to apply the local theory.
* `localRamificationIndex` and `localInertiaDegree` are the local ramification index
  and local residue degree, evaluated at the completed valuation rings.
* `finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree` is the
  **local fundamental identity**: for the completed rings, the degree of the
  completion extension is the product of the local ramification index and the local
  residue degree. Its only non-structural input is `Module.Finite 𝒪_v 𝒪_w`.
* `finrank_adicCompletion_eq_relativeCompletionDegree` transfers that identity to the
  library data of the number-field extension, taking as named hypotheses the two
  comparisons of the local data with `relativeRamificationIndex` /
  `relativeResidueDegree`; the special cases `e = 1`, `f = 1` and degree one are
  recorded as corollaries.
* `relativeResidueDegree_le_finrank_adicCompletion` and
  `relativeRamificationIndex_le_finrank_adicCompletion` are the one-sided bounds
  obtained when only one of the two comparisons is available.
* `relativeCompletionDegree_le_fieldDegree` is an *unconditional* bound:
  `e * f ≤ [K : k]`, obtained from Mathlib's `Ideal.sum_ramification_inertia` at the
  fibre of the contracted place. `one_le_finrank_adicCompletion` and
  `relativeCompletionDegree_eq_one_iff` are the remaining unconditional degree facts.
* `integralClosure_le_adicCompletionIntegers` proves one half of the finiteness input
  unconditionally: every element of `K_w` integral over `𝒪_v` lies in `𝒪_w`.
  `moduleFinite_adicCompletionIntegers_of_isIntegralClosure` shows that the
  `IsIntegralClosure` statement, i.e. the converse inclusion, suffices to obtain
  `Module.Finite 𝒪_v 𝒪_w` from Mathlib's `IsIntegralClosure.finite`.

Honest scope. This file does **not** prove `Module.finrank k_v K_w = e * f`
unconditionally. Two independent inputs are missing from Mathlib 4.32.2 and are stated
as explicit hypotheses, never as axioms or placeholders:

1. `Module.Finite 𝒪_v 𝒪_w` for the completed valuation rings. Equivalently, `𝒪_w` is
   the integral closure of `𝒪_v` in `K_w`, which is the unique-extension theorem for a
   complete valuation; Mathlib has `IsIntegralClosure.finite` but no
   `IsIntegralClosure 𝒪_w 𝒪_v K_w`. The inclusion
   `integralClosure 𝒪_v K_w ≤ 𝒪_w` is proved here; only the converse is missing.
2. The identification of the local ramification index and local residue degree with
   `relativeRamificationIndex` and `relativeResidueDegree`. Mathlib has no
   residue-field isomorphism `𝒪_v ⧸ 𝔪_v ≃+* 𝓞 k ⧸ v` for adic completions, and no
   invariance of `Ideal.ramificationIdx'` under adic completion
   (`Ideal.ramificationIdx'_le_ramificationIdx'` yields only an inequality, and
   `Ideal.ramificationIdx_tower` would require flatness of `𝒪_w` over `𝓞 K`).

A third, independent global obstruction noted in the consumer file is the local-global
degree formula `∑_{w | v} [K_w : k_v] = [K : k]`; only `≤` is available here. None of
the three is assumed anywhere in a proved statement: they appear only as hypotheses of
the transfer theorems, so every declaration below is fully proved from its hypotheses.
-/

open scoped Valued

namespace LeanFormal.IUT

universe u v

namespace NumberFieldFinitePlace

noncomputable section

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ## Algebra structures on the completed local fields and rings -/

/-- The upper completion as an algebra over the lower completion, through the actual
completion embedding. This global instance is the same structure as
`completionAlgebra` of `FinitePlaceCompletionNormTransport`, made available to type
class inference. -/
noncomputable instance instAlgebraAdicCompletion (place : NumberField.FinitePlace K) :
    Algebra ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
  (completionMap (k := k) place).toAlgebra

theorem algebraMap_instAlgebraAdicCompletion (place : NumberField.FinitePlace K) :
    (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K)) = completionMap (k := k) place :=
  rfl

/-- The upper completed valuation ring as an algebra over the lower completed
valuation ring, through the induced map on completed valuation rings. -/
noncomputable instance instAlgebraAdicCompletionIntegers (place : NumberField.FinitePlace K) :
    Algebra ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) :=
  (completionIntegersMap (k := k) place).toAlgebra

theorem algebraMap_instAlgebraAdicCompletionIntegers (place : NumberField.FinitePlace K) :
    (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) =
      completionIntegersMap (k := k) place :=
  rfl

/-- The upper completion as an algebra over the lower *completed valuation ring*,
obtained by composing the two algebra maps. -/
noncomputable instance instAlgebraAdicCompletionIntegersCompletion
    (place : NumberField.FinitePlace K) :
    Algebra ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K) :=
  (((algebraMap ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K)).comp
      (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        ((comap (k := k) place).maximalIdeal.adicCompletion k)))).toAlgebra

theorem algebraMap_instAlgebraAdicCompletionIntegersCompletion
    (place : NumberField.FinitePlace K) :
    (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K)) =
      (completionMap (k := k) place).comp
        (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
          ((comap (k := k) place).maximalIdeal.adicCompletion k)) :=
  rfl

/-- The algebra map on completed valuation rings is a local homomorphism: a nonunit of
the lower completed valuation ring stays a nonunit of the upper one. This registers the
upstream theorem `isLocalHom_completionIntegersMap` for the algebra structure
`instAlgebraAdicCompletionIntegers`, so that Mathlib's local theory of the completed
valuation rings (e.g. `IsLocalRing.ResidueField.map`, residue-field transport) applies
to this algebra map without introducing a local instance at each use site. -/
instance instIsLocalHomAdicCompletionIntegers (place : NumberField.FinitePlace K) :
    IsLocalHom (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) := by
  rw [algebraMap_instAlgebraAdicCompletionIntegers (k := k) place]
  exact isLocalHom_completionIntegersMap (k := k) place

/-- The algebra map on completed valuation rings is injective; equivalently, the upper
completed valuation ring is a faithful module over the lower one. This registers the
upstream theorem `completionIntegersMap_injective` at the algebra structure. -/
instance instFaithfulSMulAdicCompletionIntegers (place : NumberField.FinitePlace K) :
    FaithfulSMul ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [algebraMap_instAlgebraAdicCompletionIntegers (k := k) place]
    exact completionIntegersMap_injective (k := k) place)

/-! ## Scalar towers for the completed local rings -/

/-- The scalar tower `𝒪_v → k_v → K_w` is compatible: acting first on the lower
completion and then passing to the upper completion is the same as passing to the
upper completion first. -/
instance instIsScalarTowerAdicCompletionIntegers (place : NumberField.FinitePlace K) :
    IsScalarTower ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The scalar tower `𝒪_v → 𝒪_w → K_w` is compatible. -/
instance instIsScalarTowerAdicCompletionIntegersRing (place : NumberField.FinitePlace K) :
    IsScalarTower ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)
      (place.maximalIdeal.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)

/-! ## Local ramification index and local residue degree -/

/-- The **local ramification index** of the finite-place extension: the ramification
index of the extension of completed valuation rings `𝒪_v → 𝒪_w`. -/
def localRamificationIndex (place : NumberField.FinitePlace K) : ℕ :=
  (IsLocalRing.maximalIdeal
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)).ramificationIdx'
    (IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K))

/-- The **local residue degree** of the finite-place extension: the inertia degree of
the extension of completed valuation rings `𝒪_v → 𝒪_w`. -/
def localInertiaDegree (place : NumberField.FinitePlace K) : ℕ :=
  (IsLocalRing.maximalIdeal
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)).inertiaDeg'
    (IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K))

/-! ## The local fundamental identity -/

/-- **Local fundamental identity.** If the upper completed valuation ring is a finite
module over the lower one, then the degree of the completion extension is the product
of the local ramification index and the local residue degree.

This is Mathlib's `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` applied to the
completed valuation rings; the only mathematical input beyond the completed local
theory is the finiteness hypothesis. -/
theorem finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      localRamificationIndex (k := k) place * localInertiaDegree (k := k) place := by
  haveI := hfinite
  refine (Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (place.maximalIdeal.adicCompletionIntegers K)
    ((comap (k := k) place).maximalIdeal.adicCompletion k)
    (place.maximalIdeal.adicCompletion K) ?_).symm
  exact IsDiscreteValuationRing.not_a_field _

/-! ## The finiteness input for the completed valuation rings -/

/-- Integrality passes from the lower completed valuation ring to the upper one: the
local embeddings form an algebra tower `𝒪_v → 𝒪_w → K_w`. -/
theorem isIntegral_adicCompletionIntegers_of_isIntegral (place : NumberField.FinitePlace K)
    {x : place.maximalIdeal.adicCompletion K}
    (hx : IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) x) :
    IsIntegral (place.maximalIdeal.adicCompletionIntegers K) x :=
  IsIntegral.tower_top hx

/-- **One half of the finiteness input, proved.** Every element of `K_w` which is
integral over `𝒪_v` already lies in `𝒪_w`: the unit ball of `K_w` is integrally closed
in `K_w` over itself, and integrality transfers along `𝒪_v → 𝒪_w`. Consequently the
missing input `Module.Finite 𝒪_v 𝒪_w` is exactly the converse inclusion, i.e. that every
element of `𝒪_w` is integral over `𝒪_v`. -/
theorem integralClosure_le_adicCompletionIntegers (place : NumberField.FinitePlace K) :
    (integralClosure ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletion K) : Set (place.maximalIdeal.adicCompletion K)) ⊆
      (place.maximalIdeal.adicCompletionIntegers K :
        Set (place.maximalIdeal.adicCompletion K)) := by
  intro x hx
  have hle : Valued.v x ≤ 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
        K place.maximalIdeal).isIntegral_iff_v_le_one.mp
      (isIntegral_adicCompletionIntegers_of_isIntegral (k := k) place hx)
  exact hle

/-- **Sufficient condition for the finiteness input.** If the completed upper valuation
ring is the integral closure of the completed lower one in `K_w`, then
`𝒪_w` is a finite `𝒪_v`-module, by Mathlib's `IsIntegralClosure.finite`. This isolates
the missing input as the `IsIntegralClosure` statement, which Mathlib 4.32.2 does not
supply for adic completions. -/
theorem moduleFinite_adicCompletionIntegers_of_isIntegralClosure
    (place : NumberField.FinitePlace K)
    (hseparable : Algebra.IsSeparable
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K))
    (hclosure : IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K)) :
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) := by
  haveI := hseparable
  haveI := hclosure
  haveI : Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
    moduleFinite_completionAlgebra (k := k) place
  exact IsIntegralClosure.finite
    ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
    ((comap (k := k) place).maximalIdeal.adicCompletion k)
    (place.maximalIdeal.adicCompletion K)
    (place.maximalIdeal.adicCompletionIntegers K)

/-! ## Unconditional degree facts -/

/-- The completion extension has positive degree: the lower completion embeds into the
upper one. -/
theorem one_le_finrank_adicCompletion (place : NumberField.FinitePlace K) :
    1 ≤ Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) := by
  haveI : Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
    moduleFinite_completionAlgebra (k := k) place
  haveI : Nontrivial (place.maximalIdeal.adicCompletion K) := inferInstance
  exact Module.finrank_pos

/-- The relative completion degree is one exactly when the extension is both
unramified and residue-degree one. -/
theorem relativeCompletionDegree_eq_one_iff (place : NumberField.FinitePlace K) :
    relativeCompletionDegree (k := k) place = 1 ↔
      relativeRamificationIndex (k := k) place = 1 ∧
        relativeResidueDegree (k := k) place = 1 := by
  rw [relativeCompletionDegree, mul_eq_one]

/-- The library relative degree `e * f` is bounded by the global degree `[K : k]`;
this is Mathlib's `Ideal.sum_ramification_inertia` specialized to the fibre of the
contracted place. -/
theorem relativeCompletionDegree_le_fieldDegree (place : NumberField.FinitePlace K) :
    relativeCompletionDegree (k := k) place ≤ Module.finrank k K := by
  let p := (comap (k := k) place).maximalIdeal.asIdeal
  have hp0 : p ≠ ⊥ := (comap (k := k) place).maximalIdeal.ne_bot
  have hmem : place.maximalIdeal.asIdeal ∈
      IsDedekindDomain.primesOverFinset p (NumberField.RingOfIntegers K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (NumberField.RingOfIntegers K)).mpr
      ⟨place.maximalIdeal.isPrime, inferInstance⟩
  have hsum : (∑ P ∈ IsDedekindDomain.primesOverFinset p (NumberField.RingOfIntegers K),
        p.ramificationIdx' P * p.inertiaDeg' P) = Module.finrank k K :=
    Ideal.sum_ramification_inertia (R := NumberField.RingOfIntegers k)
      (S := NumberField.RingOfIntegers K) (K := k) (L := K) (p := p) hp0
  rw [← hsum]
  exact Finset.single_le_sum (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P)
    (fun _ _ => Nat.zero_le _) hmem

/-! ## Local data versus the library data of the place extension -/

/-- The statement that the local data of the completed extension agree with the
library data of the finite-place extension. This is the second named input of
`finrank_adicCompletion_eq_relativeCompletionDegree`; it is *not* proved in this
file (Mathlib 4.32.2 has no comparison of the residue fields or of
`Ideal.ramificationIdx'` across an adic completion). -/
def localDataAgreesWithPlaceData (place : NumberField.FinitePlace K) : Prop :=
  localRamificationIndex (k := k) place = relativeRamificationIndex (k := k) place ∧
    localInertiaDegree (k := k) place = relativeResidueDegree (k := k) place

/-- **Transfer of the local fundamental identity to the place data.** Assuming that the
completed valuation rings form a finite module extension and that the local ramification
index and local residue degree agree with the library data at the number rings, the
degree of the completion extension is the relative degree `e * f` of the place
extension. -/
theorem finrank_adicCompletion_eq_relativeCompletionDegree
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K))
    (hagree : localDataAgreesWithPlaceData (k := k) place) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeCompletionDegree (k := k) place := by
  obtain ⟨hramification, hresidue⟩ := hagree
  rw [finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
      (k := k) place hfinite,
    hramification, hresidue, relativeCompletionDegree]

/-- Equational form of the reduction: under the finiteness hypothesis, the target
identity holds exactly when the local product `e_loc * f_loc` equals the library
product `e * f`. -/
theorem finrank_adicCompletion_eq_relativeCompletionDegree_iff
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) :
    (Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeCompletionDegree (k := k) place) ↔
      localRamificationIndex (k := k) place * localInertiaDegree (k := k) place =
        relativeRamificationIndex (k := k) place *
          relativeResidueDegree (k := k) place := by
  rw [finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
      (k := k) place hfinite,
    relativeCompletionDegree]

/-- The local ramification index of the completed extension is nonzero as soon as the
completed valuation rings form a finite module extension. -/
theorem one_le_localRamificationIndex (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) :
    1 ≤ localRamificationIndex (k := k) place := by
  have hdegree := finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
    (k := k) place hfinite
  have hpositive := one_le_finrank_adicCompletion (k := k) place
  rw [hdegree] at hpositive
  exact Nat.one_le_iff_ne_zero.mpr
    (left_ne_zero_of_mul (Nat.pos_iff_ne_zero.mp hpositive))

/-- The local residue degree of the completed extension is nonzero as soon as the
completed valuation rings form a finite module extension. -/
theorem one_le_localInertiaDegree (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) :
    1 ≤ localInertiaDegree (k := k) place := by
  have hdegree := finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
    (k := k) place hfinite
  have hpositive := one_le_finrank_adicCompletion (k := k) place
  rw [hdegree] at hpositive
  exact Nat.one_le_iff_ne_zero.mpr
    (right_ne_zero_of_mul (Nat.pos_iff_ne_zero.mp hpositive))

/-! ## General inequalities from one comparison -/

/-- If only the residue degree is known to agree with the library data, the completion
degree is still bounded below by the library residue degree. -/
theorem relativeResidueDegree_le_finrank_adicCompletion (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K))
    (hresidue : localInertiaDegree (k := k) place =
      relativeResidueDegree (k := k) place) :
    relativeResidueDegree (k := k) place ≤
      Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) := by
  rw [finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
      (k := k) place hfinite, ← hresidue]
  exact Nat.le_mul_of_pos_left _ (one_le_localRamificationIndex (k := k) place hfinite)

/-- If only the ramification index is known to agree with the library data, the
completion degree is still bounded below by the library ramification index. -/
theorem relativeRamificationIndex_le_finrank_adicCompletion (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K))
    (hramification : localRamificationIndex (k := k) place =
      relativeRamificationIndex (k := k) place) :
    relativeRamificationIndex (k := k) place ≤
      Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) := by
  rw [finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
      (k := k) place hfinite, ← hramification]
  exact Nat.le_mul_of_pos_right _ (one_le_localInertiaDegree (k := k) place hfinite)

/-! ## The special cases `e = 1`, `f = 1` and relative degree one -/

/-- Unramified case: if the local ramification index is one, the degree of the
completion extension is the library residue degree. -/
theorem finrank_adicCompletion_eq_relativeResidueDegree_of_localRamificationIndex_eq_one
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K))
    (hagree : localDataAgreesWithPlaceData (k := k) place)
    (hramification : localRamificationIndex (k := k) place = 1) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeResidueDegree (k := k) place := by
  rw [finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
      (k := k) place hfinite, hramification, one_mul, hagree.2]

/-- Residue-degree-one case: if the local residue degree is one, the degree of the
completion extension is the library ramification index. -/
theorem finrank_adicCompletion_eq_relativeRamificationIndex_of_localInertiaDegree_eq_one
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K))
    (hagree : localDataAgreesWithPlaceData (k := k) place)
    (hresidue : localInertiaDegree (k := k) place = 1) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeRamificationIndex (k := k) place := by
  rw [finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree
      (k := k) place hfinite, hresidue, mul_one, hagree.1]

/-- Relative-degree-one case: if the relative degree `e * f` of the place extension is
one, then the completion extension has degree one. -/
theorem finrank_adicCompletion_eq_one_of_relativeCompletionDegree_eq_one
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K))
    (hagree : localDataAgreesWithPlaceData (k := k) place)
    (hdegree : relativeCompletionDegree (k := k) place = 1) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) = 1 := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree (k := k) place hfinite hagree, hdegree]

end

end NumberFieldFinitePlace

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finitePlaceCompletionLocalStructure : Obligation :=
  { id := "Foundations.NumberField.finite-place-completion-local-structure"
    source :=
      "Standard local algebra of a finite extension of complete discretely valued " ++
        "fields (Serre, Local Fields, II.2)"
    status := VerificationStatus.provedKernel
    note :=
      "The upper completion is registered as a `k_v`-algebra with algebra map the " ++
        "actual completion embedding, the upper completed valuation ring is " ++
        "registered as an `𝒪_v`-algebra with algebra map the actual map on completed " ++
        "valuation rings, and the upper completion is registered as an `𝒪_v`-algebra " ++
        "through the composite. The two scalar towers `𝒪_v -> k_v -> K_w` and " ++
        "`𝒪_v -> 𝒪_w -> K_w` are proved compatible, so Mathlib's local ramification " ++
        "and inertia theory applies to the completed rings. The local ramification " ++
        "index and local residue degree are introduced as the library " ++
        "`Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` at the completed valuation " ++
        "rings. All declarations in this group are unconditional."
    dependsOn := [ "Foundations.NumberField.finite-place-extension" ] }

def finitePlaceCompletionLocalFundamentalIdentity : Obligation :=
  { id := "Foundations.NumberField.finite-place-completion-local-fundamental-identity"
    source :=
      "Fundamental identity [L : K] = e * f for complete discretely valued fields " ++
        "(Serre, Local Fields, II.2)"
    status := VerificationStatus.conditional
    note :=
      "`finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree` " ++
        "proves `Module.finrank k_v K_w = e_loc * f_loc` for the completed valuation " ++
        "rings, from Mathlib's `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`, " ++
        "conditionally on `Module.Finite 𝒪_v 𝒪_w`. " ++
        "`finrank_adicCompletion_eq_relativeCompletionDegree` transfers this to the " ++
        "library relative degree `e * f` of the place extension, conditionally on that " ++
        "same finiteness together with the named comparison " ++
        "`localDataAgreesWithPlaceData` of the local ramification index and local " ++
        "residue degree with `relativeRamificationIndex` and " ++
        "`relativeResidueDegree`; `finrank_adicCompletion_eq_relativeCompletionDegree_iff` " ++
        "records that under finiteness the target identity is *equivalent* to the " ++
        "comparison of the two products. The one-sided bounds " ++
        "`relativeResidueDegree_le_finrank_adicCompletion` and " ++
        "`relativeRamificationIndex_le_finrank_adicCompletion`, the special cases " ++
        "`e_loc = 1`, `f_loc = 1`, `e * f = 1` and the unconditional bound " ++
        "`relativeCompletionDegree_le_fieldDegree` (`e * f <= [K : k]`, from " ++
        "`Ideal.sum_ramification_inertia`), together with " ++
        "`one_le_finrank_adicCompletion` and `relativeCompletionDegree_eq_one_iff`, " ++
        "are proved as well. `integralClosure_le_adicCompletionIntegers` proves the " ++
        "inclusion `integralClosure 𝒪_v K_w <= 𝒪_w` unconditionally, and " ++
        "`moduleFinite_adicCompletionIntegers_of_isIntegralClosure` derives the " ++
        "finiteness input from `IsIntegralClosure 𝒪_w 𝒪_v K_w` via " ++
        "`IsIntegralClosure.finite`. " ++
        "Two inputs remain unproved in Mathlib 4.32.2 and are " ++
        "hypotheses only: `Module.Finite 𝒪_v 𝒪_w` (equivalently the identification of " ++
        "`𝒪_w` with the integral closure of `𝒪_v` in `K_w`, i.e. uniqueness of the " ++
        "extension of a complete valuation) and `localDataAgreesWithPlaceData` (no " ++
        "residue-field isomorphism `𝒪_v ⧸ 𝔪_v ≃+* 𝓞 k ⧸ v` and no invariance of " ++
        "`Ideal.ramificationIdx'` under adic completion). The unconditional identity " ++
        "`Module.finrank k_v K_w = e * f` is therefore *not* claimed here; no " ++
        "placeholder declaration and no external axiom is introduced."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-completion-norm-transport",
        "Foundations.NumberField.finite-place-completion-local-structure" ]
    externalAxioms := []
    sorryItems := [] }

end LeanFormal.IUT.Audit
