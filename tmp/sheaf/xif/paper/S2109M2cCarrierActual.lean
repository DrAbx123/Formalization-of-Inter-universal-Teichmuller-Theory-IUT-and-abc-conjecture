import tmp.sheaf.xif.paper.S2102TorsionArtinActual

/-!
# S2109: the M2c carrier comparison -- exact reduction and first missing

Layer: **O** (original Theta-link / q-pilot).  Consumers: S2027's
`canonicalTorsionComparison` / `profiniteTorsionComparison`, S2046/S2103's
`LocalArtinSourceData.carrier`, and through them S2011/S2024's levelwise
local reciprocity on torsion.

## The target

For an open subgroup `U` of `G_v = Gal(Qbar_p/Q_p)` (so `U = Gal(Qbar_p/L)`
with `L = FixedField U`), S2027 asks for

  `canonicalTorsionComparison p U` :
    `Function.Bijective (torsionMap (abelianizationToTopological p U))`,

where `abelianizationToTopological p U : Abelianization ↥U →*
TopologicalAbelianization (localGaloisGroup p U)` is the canonical map between
Mathlib's *abstract* abelianization `U / [U,U]` and the *profinite*
abelianization `U / closure [U,U]`.  The equivalence form is

  `CarrierComparison U` :
    `CommGroup.torsion (Abelianization ↥U) ≃*
      CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))`.

## What this file proves unconditionally

1.  **General torsion calculus** (`torsionMap_injective_iff`,
    `torsionMap_surjective_iff`, `torsionMap_bijective_iff`): for a
    homomorphism `f : A →* B` of commutative groups, injectivity of
    `torsionMap f` is *exactly* torsion-freeness of `ker f`, and
    surjectivity is *exactly* the statement that every torsion element of `B`
    lifts to a torsion element of `A`.  Neither is automatic for a
    surjective `f`; this is the precise group-theoretic shape of M2c.

2.  **The closure criterion** (`CommutatorClosed`): if the abstract
    commutator subgroup of `localGaloisGroup p U` is already closed, then
    `abelianizationToTopological p U` is a group isomorphism
    (`abelianizationToTopological_bijective_of_commutatorClosed`, with an
    explicit inverse `abelianizationFromTopological`), hence

      `canonicalTorsionComparison_of_commutatorClosed`,
      `carrierComparison_of_commutatorClosed`  (the exact M2c type),
      `profiniteTorsionComparison_of_commutatorClosed`,
      `localArtinSourceDataOfCommutatorClosed` (the M2c consumer in S2027).

    These are genuine proofs, not assumptions: no field of
    `LocalArtinSourceData` is fabricated, the extra input is an explicit
    argument of each theorem.

3.  **The exact first missing** (`M2cFirstMissing`): the single
    group-theoretic input that is *not* available in the tree,

      `∀ U, (commutator (localGaloisGroup p U)).topologicalClosure
              = commutator (localGaloisGroup p U)`.

    Equivalently: the abstract commutator subgroup `[U,U]` of the open
    subgroup is closed, i.e. `U/[U,U] = U/closure [U,U]`.

## Why the missing input cannot be produced from the general theory

`CommutatorClosed` is *not* a general fact about topological or profinite
groups, and the torsion comparison is *not* a formal consequence of the
abelianization construction.  Two honest reasons, recorded so that the gap is
not mistaken for a missing `simp` lemma:

* Closedness of `[G,G]` is a genuine condition, not a formality: the abstract
  commutator subgroup is only the union of the images `C_n` of the compact
  sets `(G × G)^n` under the commutator-product map.  Each `C_n` is compact
  (hence closed), but a countable union of closed sets need not be closed, and
  the information "lies in the closure" is exactly the information visible in
  all finite quotients.  For a profinite group, closedness of `[G,G]` is
  equivalent to injectivity of `G^ab → G/\overline{[G,G]}`.  It fails for
  general compact/profinite groups: the standard examples are products
  `∏_n H_n` of finite groups of unbounded commutator width, where the
  coordinatewise element of `∏_n [H_n,H_n]` needing `n` commutators in
  coordinate `n` lies in the closure but is not a finite product of
  commutators.  Hence no argument using only compactness, finite quotients, or
  the universal property of the abelianization can give M2c; the *specific*
  group `Gal(Qbar_p/L)` must be used.

* Closedness of `[G,G]` is a genuine condition, not a formality.  The abstract
  commutator subgroup is only the union of the images `C_n` of the compact
  sets `(G × G)^n` under the commutator-product map; each `C_n` is compact
  (hence closed), but a countable union of closed sets need not be closed, and
  the information "lies in the closure" is exactly the information visible in
  all finite quotients.  For a profinite group, closedness of `[G,G]` is
  equivalent to injectivity of `G^ab → G/\overline{[G,G]}`.  General compact
  groups need not satisfy it (products of finite groups whose elements need
  unbounded numbers of commutators are the standard source of examples), so no
  argument using only compactness, finite quotients, or the universal property
  of the abelianization can give M2c; the *specific* group `Gal(Qbar_p/L)`
  must be used.

* For `G_L = Gal(Qbar_p/L)` the relevant available input would be a
  strong-completeness theorem for finitely generated profinite groups
  (Nikolov--Segal: every finite-index subgroup is open), which is the kind of
  deep structure result that forces such agreement.  It is **not** in Mathlib
  v4.32.2, and nothing in the tree (S2027, S2017, S2093, S2102, the LANA
  local-CFT port) proves closedness of `[G_L,G_L]` or any equivalent
  statement.  This file therefore records the closedness form (which is exactly
  what the proofs below consume) as `M2cFirstMissing`, never assumed.

## Status (honest)

* `canonicalTorsionComparison` is **not proved unconditionally** here.
* `carrierComparison_of_commutatorClosed` is a complete unconditional proof
  *modulo the named hypothesis* `CommutatorClosed`; it is not an instance,
  axiom, or change of target.
* No `sorry`, `admit`, `axiom` or `opaque` is introduced.  Axiom probes
  are at the end of the file.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LeanFormal.IUT.XiFPaper.S2109M2cCarrierActual

open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2102TorsionArtinActual

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : Index p)

/-! ## 1. The surfaces of M2c -/

/-- The canonical comparison map, on torsion subgroups.  This is the map whose
bijectivity is S2027's `canonicalTorsionComparison`. -/
noncomputable abbrev canonicalMap :
    CommGroup.torsion (Abelianization ↥U) →*
      CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)) :=
  torsionMap (abelianizationToTopological p U)

/-- The equivalence form of M2c, at its exact type. -/
abbrev CarrierComparison : Type :=
  CommGroup.torsion (Abelianization ↥U) ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))

/-- S2027's canonical propositional surface for M2c. -/
abbrev CanonicalCarrierComparison : Prop := canonicalTorsionComparison p U

/-! ## 2. General torsion calculus (no local field involved)

For a homomorphism `f : A →* B` of commutative groups, `torsionMap f` is the
restriction of `f` to torsion.  The two lemmas below identify *exactly* what
injectivity and surjectivity of that restriction mean.  They are the precise
group-theoretic content of "(M2c) on torsion" and show that neither direction
is formal. -/

/-- **Injectivity criterion.**  `torsionMap f` is injective exactly when the
kernel of `f` has no nontrivial torsion. -/
theorem torsionMap_injective_iff {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) :
    Function.Injective (torsionMap f) ↔
      ∀ x : A, f x = 1 → IsOfFinOrder x → x = 1 := by
  constructor
  · intro hf x hx hfin
    have h1 : torsionMap f ⟨x, hfin⟩ = 1 := by
      apply Subtype.ext
      exact hx
    have h2 : (⟨x, hfin⟩ : CommGroup.torsion A) = 1 :=
      hf (by rw [map_one]; exact h1)
    simpa using Subtype.ext_iff.mp h2
  · intro hf x y hxy
    have hxy' : f (x : A) = f (y : A) := by
      exact Subtype.ext_iff.mp hxy
    have hdiv : f ((x : A) * (y : A)⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy', mul_inv_cancel]
    have hfin : IsOfFinOrder ((x : A) * (y : A)⁻¹) :=
      IsOfFinOrder.mul x.2 (IsOfFinOrder.inv y.2)
    have hone : (x : A) * (y : A)⁻¹ = 1 := hf _ hdiv hfin
    refine Subtype.ext ?_
    calc (x : A) = (x : A) * (y : A)⁻¹ * (y : A) := by group
      _ = 1 * (y : A) := by rw [hone]
      _ = (y : A) := one_mul _

/-- **Surjectivity criterion.**  `torsionMap f` is surjective exactly when
every torsion element of the target lifts to a torsion element of the source.
(Surjectivity of `f` alone does not suffice: `ℤ → ℤ/2`.) -/
theorem torsionMap_surjective_iff {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) :
    Function.Surjective (torsionMap f) ↔
      ∀ y : B, IsOfFinOrder y → ∃ x : A, IsOfFinOrder x ∧ f x = y := by
  constructor
  · intro hf y hy
    obtain ⟨x, hx⟩ := hf ⟨y, hy⟩
    exact ⟨(x : A), x.2, Subtype.ext_iff.mp hx⟩
  · intro hf y
    obtain ⟨x, hxfin, hxy⟩ := hf (y : B) y.2
    exact ⟨⟨x, hxfin⟩, Subtype.ext hxy⟩

/-- **Bijectivity criterion**: both conditions at once. -/
theorem torsionMap_bijective_iff {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) :
    Function.Bijective (torsionMap f) ↔
      (∀ x : A, f x = 1 → IsOfFinOrder x → x = 1) ∧
      (∀ y : B, IsOfFinOrder y → ∃ x : A, IsOfFinOrder x ∧ f x = y) := by
  rw [Function.Bijective, torsionMap_injective_iff, torsionMap_surjective_iff]

/-- A bijective homomorphism induces a bijection on torsion. -/
theorem torsionMap_bijective_of_bijective {A B : Type*} [CommGroup A] [CommGroup B]
    {f : A →* B} (hf : Function.Bijective f) :
    Function.Bijective (torsionMap f) := by
  constructor
  · intro x y hxy
    refine Subtype.ext (hf.1 ?_)
    exact Subtype.ext_iff.mp hxy
  · intro y
    obtain ⟨x, hx⟩ := hf.2 (y : B)
    have hfin : IsOfFinOrder x :=
      (Function.Injective.isOfFinOrder_iff (f := f) hf.1).mp (hx ▸ y.2)
    exact ⟨⟨x, hfin⟩, Subtype.ext hx⟩

/-! ## 3. The exact missing group-theoretic input -/

/-- **The closedness of the abstract commutator subgroup** of
`localGaloisGroup p U = Gal(Qbar_p / L)`.

This is the single group-theoretic input that separates the abstract
abelianization `U/[U,U]` from the profinite one `U/closure [U,U]`.  It is the
exact first missing statement for M2c: it is not in Mathlib, not in the tree,
and not a general fact about compact or profinite groups (see the module
docstring).  It is recorded as a `def`, never assumed and never inhabited. -/
def CommutatorClosed : Prop :=
  (commutator (localGaloisGroup p U)).topologicalClosure =
    commutator (localGaloisGroup p U)

/-! ## 4. Unconditional: the inverse map and the group isomorphism -/

/-- Under `CommutatorClosed`, the abstract commutator is the whole kernel of
the quotient map, so the canonical comparison has an explicit inverse: the
reciprocity-side map `Ab_topo → Ab`, induced by `Abelianization.of` composed
with the identification `U ≅ Gal(Qbar_p/L)`. -/
noncomputable def abelianizationFromTopological (h : CommutatorClosed U) :
    TopologicalAbelianization (localGaloisGroup p U) →* Abelianization ↥U :=
  QuotientGroup.lift ((commutator (localGaloisGroup p U)).topologicalClosure)
    ((Abelianization.of).comp (localGaloisGroupEquiv p U).symm.toMonoidHom)
    (by
      rw [h]
      exact Abelianization.commutator_subset_ker _)

/-- One inverse law: the inverse map is a left inverse of the canonical map. -/
theorem abelianizationFromTopological_comp_canonical (h : CommutatorClosed U) :
    (abelianizationFromTopological U h).comp (abelianizationToTopological p U) =
      MonoidHom.id _ := by
  apply Abelianization.hom_ext
  ext u
  simp [abelianizationFromTopological, abelianizationToTopological]

/-- The other inverse law. -/
theorem canonical_comp_abelianizationFromTopological (h : CommutatorClosed U) :
    (abelianizationToTopological p U).comp (abelianizationFromTopological U h) =
      MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext ((commutator (localGaloisGroup p U)).topologicalClosure)
  ext g
  simp [abelianizationFromTopological, abelianizationToTopological]

/-- **The canonical map is a group isomorphism once the abstract commutator
subgroup is closed.** -/
theorem abelianizationToTopological_bijective_of_commutatorClosed
    (h : CommutatorClosed U) :
    Function.Bijective (abelianizationToTopological p U) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨abelianizationFromTopological U h, ?_, ?_⟩
  · intro x
    have h1 := DFunLike.congr_fun (abelianizationFromTopological_comp_canonical U h) x
    simpa using h1
  · intro y
    have h1 := DFunLike.congr_fun (canonical_comp_abelianizationFromTopological U h) y
    simpa using h1

/-- **M2c on torsion, from commutator closedness.** -/
theorem canonicalTorsionComparison_of_commutatorClosed (h : CommutatorClosed U) :
    canonicalTorsionComparison p U :=
  torsionMap_bijective_of_bijective
    (abelianizationToTopological_bijective_of_commutatorClosed U h)

/-- **The sharp torsion-level form of M2c.**  The carrier comparison holds as
soon as the canonical map has torsion-free kernel and torsion lifts; these two
conditions are *equivalent* to M2c by `torsionMap_bijective_iff`, and
`CommutatorClosed` is a sufficient condition for both.  This isolates the
exact content that a future proof of the missing statement must supply. -/
noncomputable def carrierComparison_of_torsionCriteria
    (hinj : ∀ x : Abelianization ↥U,
      abelianizationToTopological p U x = 1 → IsOfFinOrder x → x = 1)
    (hsurj : ∀ y : TopologicalAbelianization (localGaloisGroup p U), IsOfFinOrder y →
      ∃ x : Abelianization ↥U, IsOfFinOrder x ∧ abelianizationToTopological p U x = y) :
    CarrierComparison U :=
  MulEquiv.ofBijective (canonicalMap U)
    ((torsionMap_bijective_iff (abelianizationToTopological p U)).mpr ⟨hinj, hsurj⟩)

/-- **The M2c carrier comparison at its exact type**, from commutator
closedness.  This is a real term of the requested equivalence type; its
underlying map is `canonicalMap`. -/
noncomputable def carrierComparison_of_commutatorClosed (h : CommutatorClosed U) :
    CarrierComparison U :=
  MulEquiv.ofBijective (canonicalMap U)
    (canonicalTorsionComparison_of_commutatorClosed U h)

/-- S2027's existential form, from commutator closedness. -/
theorem profiniteTorsionComparison_of_commutatorClosed (h : CommutatorClosed U) :
    profiniteTorsionComparison p U :=
  ⟨carrierComparison_of_commutatorClosed U h⟩

/-- The M2c consumer: S2027's `LocalArtinSourceData` (with M2a taken
unconditionally from S2102) once commutator closedness is known for every open
subgroup.  The `carrier` field is supplied, not assumed. -/
noncomputable def localArtinSourceDataOfCommutatorClosed
    (h : ∀ U : Index p, CommutatorClosed U) : LocalArtinSourceData p where
  artin := fun U => S2046M2TorsionRequired_actual U
  carrier := fun U => carrierComparison_of_commutatorClosed U (h U)

/-! ## 5. The named missing statement -/

/-- **The exact first missing statement of M2c**: commutator closedness for all
open subgroups `U` of `G_v`.

This is the only input required by the proofs above.  It is not derivable from
Mathlib v4.32.2 nor from the tree (S2027/S2017/S2093/S2102/the LANA port); the
torsion comparison itself is *not* claimed. -/
def M2cFirstMissing : Prop := ∀ U : Index p, CommutatorClosed U

/-- The missing statement is exactly what the M2c consumer needs: it yields the
carrier comparison for every level. -/
theorem carrierComparison_of_firstMissing (h : M2cFirstMissing (p := p)) :
    ∀ U : Index p, Nonempty (CarrierComparison U) :=
  fun U => ⟨carrierComparison_of_commutatorClosed U (h U)⟩

/-! ## 6. The conditional term has exactly the requested type -/

/-- The M2c carrier comparison, at the type requested in the task, conditional
on the named missing statement.  This is a definitional type check: the
conclusion is literally `CommGroup.torsion (Abelianization ↥U) ≃*
CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))`. -/
example (h : CommutatorClosed U) :
    CommGroup.torsion (Abelianization ↥U) ≃*
      CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)) :=
  carrierComparison_of_commutatorClosed U h

/-- The missing hypothesis is not a change of target: dropping it leaves the
statement of M2c itself. -/
example : CanonicalCarrierComparison U ↔
    Function.Bijective (torsionMap (abelianizationToTopological p U)) :=
  Iff.rfl

/-! ## 7. Axiom probes -/

#print axioms torsionMap_injective_iff
#print axioms torsionMap_surjective_iff
#print axioms torsionMap_bijective_iff
#print axioms torsionMap_bijective_of_bijective
#print axioms abelianizationFromTopological
#print axioms abelianizationFromTopological_comp_canonical
#print axioms canonical_comp_abelianizationFromTopological
#print axioms abelianizationToTopological_bijective_of_commutatorClosed
#print axioms canonicalTorsionComparison_of_commutatorClosed
#print axioms carrierComparison_of_torsionCriteria
#print axioms carrierComparison_of_commutatorClosed
#print axioms profiniteTorsionComparison_of_commutatorClosed
#print axioms localArtinSourceDataOfCommutatorClosed
#print axioms carrierComparison_of_firstMissing

end LeanFormal.IUT.XiFPaper.S2109M2cCarrierActual
