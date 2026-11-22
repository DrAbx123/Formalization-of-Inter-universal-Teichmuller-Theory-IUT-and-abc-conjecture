import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitUnitsActionSupply
import Mathlib.Tactic

/-!
# Unconditional factorization provider for the κ-orbit source data (IUT II, Definition 4.9)

The strip-side conditional constructor
(`IUTII/Frobenioid/PrimeStripUnitsActionFactorization.lean`) consumes a
factorization `g : ∀ v, G →* toDPrimeStrip.Pi v` of an abstract group `G`
through the local groups of an F-prime-strip and produces the units action
`(F.unitsAction v).comp (g v)`.  The present file supplies the factorization
itself, unconditionally, for every F-prime-strip and every strip pair:

* `FPrimeStrip.evaluationFactorization` — the canonical family of evaluation
  maps from the product of the strip's local groups onto each local group;
* `FPrimeStrip.piTupleHom` and
  `FPrimeStrip.evaluationFactorization_comp_piTupleHom` — universality: every
  family of homomorphisms `g : ∀ v, G →* Pi v` is the composite of the
  canonical evaluation family with the tuple homomorphism
  `G →* (∀ v, Pi v)`, so the canonical provider subsumes every other
  source-data provider at the level of the factorization;
* `FPrimeStrip.universalKappaOrbitUnitsActionDatum` — the unconditional
  inhabitant of `KappaOrbitUnitsActionDatum` (IUT II, Definition 4.9, (i))
  for an arbitrary F-prime-strip, on the product of its local groups;
* `FPrimeStrip.pairFactorizationUpper` / `pairFactorizationLower` /
  `pairTupleHom` — a common group for a strip pair with both evaluation
  factorizations, together with the ready-made `sourceAction` / `targetAction`
  shapes `FPrimeStrip.pairUnitsActionUpper` / `pairUnitsActionLower` of the
  SHE consumption slots (`SourceKummerEvaluationArrows.lean`, cards LK/EV).

Paper anchors: IUT II, Definition 4.9, (ii) identifies the group acting on a
split Frobenioid with `Aut(‡A)` [a profinite group isomorphic to `Gw`]; the
group-theoretic algorithms `G ↦→ (G ↷ O^x(G))` and `G ↦→ (G ↷ O^{x mu}(G))`
of IUT II, Example 1.8, (iii), (iv), are functorial in the topological group
`G` itself, so a factorization of an abstract `G` through the strip's local
groups is exactly the datum through which `G` meets the strip.

## Faithfulness boundary (explicit)

The provider's group is the canonical *universal* choice (the product of the
local groups), equipped with the evaluation factorization.  This discharges
unconditionally the existence face of the `G1-SRC-a` actions sub-obligation
at the reduced interface.  It does NOT identify this group with the paper's
`‡G = Aut(‡A) ≅ Gw` of IUT II, Definition 4.9, (ii), nor construct the
group-theoretic algorithms of Example 1.8, (iii), (iv): that identification
needs the split-Frobenioid universal covering, the `2l`-torsion and the
splittings, which are not constructed in this repository.  By universality,
the factorization of any other source-data provider `(G, g)` is the composite
of the canonical evaluation family with its tuple homomorphism, so no other
supply shape can exceed the canonical one at the reduced interface.
-/

namespace LeanFormal.IUT

universe uG uV

namespace FPrimeStrip

/-- Fallback topology on the product of a strip's local groups: the
indiscrete topology.  It is used only when no finer (e.g. product) topology
is available for the factors; the κ-orbit datum built below does not depend
on this choice. -/
noncomputable instance productPiTopology {V : Type uV} (F : FPrimeStrip V) :
    TopologicalSpace ((v : V) → F.toDPrimeStrip.Pi v) :=
  ⊥

variable {V : Type uV} (F : FPrimeStrip V)

/-- The canonical evaluation factorization of the product of the local groups
of a strip: at each place `v`, evaluation of a family of local group elements
at `v`. -/
def evaluationFactorization :
    ∀ v : V, ((v : V) → F.toDPrimeStrip.Pi v) →* F.toDPrimeStrip.Pi v :=
  fun v =>
    { toFun := fun f => f v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp] theorem evaluationFactorization_apply
    (v : V) (f : (v : V) → F.toDPrimeStrip.Pi v) :
    F.evaluationFactorization v f = f v := rfl

/-- The tuple homomorphism of a family `g : ∀ v, G →* Pi v`. -/
def piTupleHom {G : Type uG} [Group G]
    (g : ∀ v : V, G →* F.toDPrimeStrip.Pi v) :
    G →* ((v : V) → F.toDPrimeStrip.Pi v) where
  toFun γ := fun v => g v γ
  map_one' := by
    funext v
    exact (g v).map_one
  map_mul' γ δ := by
    funext v
    exact (g v).map_mul γ δ

@[simp] theorem piTupleHom_apply {G : Type uG} [Group G]
    (g : ∀ v : V, G →* F.toDPrimeStrip.Pi v) (γ : G) (v : V) :
    F.piTupleHom g γ v = g v γ := rfl

/-- Universality of the canonical provider: every family of homomorphisms
`g : ∀ v, G →* Pi v` is the composite of the evaluation family with the tuple
homomorphism. -/
theorem evaluationFactorization_comp_piTupleHom {G : Type uG} [Group G]
    (g : ∀ v : V, G →* F.toDPrimeStrip.Pi v) (v : V) :
    (F.evaluationFactorization v).comp (F.piTupleHom g) = g v := by
  ext γ
  rfl

/-- The unconditional κ-orbit datum of IUT II, Definition 4.9, for an
arbitrary F-prime-strip: on the product of the strip's local groups, by
canonical completion of the evaluation factorization. -/
noncomputable def universalKappaOrbitUnitsActionDatum :
    KappaOrbitUnitsActionDatum ((v : V) → F.toDPrimeStrip.Pi v) F :=
  KappaOrbitUnitsActionDatum.canonicalDatumOfFactorization
    F.evaluationFactorization

@[simp] theorem universalKappaOrbitUnitsActionDatum_factor (v : V) :
    F.universalKappaOrbitUnitsActionDatum.factor v =
      F.evaluationFactorization v := rfl

set_option linter.defProp false in
/-- Existence form: every F-prime-strip carries an inhabitant of the κ-orbit
datum on its canonical product group.  The statement type is inferred from the
canonical datum, which pins the `sourceUnits` carrier universe to that of
`(F.Mon v)ˣ`; a written-out header would freeze a free `sourceUnits` universe
before the value is checked (Lean generalizes theorem-head universes eagerly),
and that stronger statement is not inhabited. -/
@[implicit_reducible] noncomputable def universalKappaOrbitUnitsActionDatum_nonempty :=
  Nonempty.intro F.universalKappaOrbitUnitsActionDatum

/-- Common-group form of the evaluation factorization for a strip pair:
projection onto the upper factor at each place. -/
def pairFactorizationUpper (upper lower : FPrimeStrip V) :
    ∀ v : V, ((v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v) →*
      upper.toDPrimeStrip.Pi v :=
  fun v =>
    { toFun := fun f => (f v).1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- Common-group form of the evaluation factorization for a strip pair:
projection onto the lower factor at each place. -/
def pairFactorizationLower (upper lower : FPrimeStrip V) :
    ∀ v : V, ((v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v) →*
      lower.toDPrimeStrip.Pi v :=
  fun v =>
    { toFun := fun f => (f v).2
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp] theorem pairFactorizationUpper_apply (upper lower : FPrimeStrip V)
    (v : V) (f : (v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v) :
    pairFactorizationUpper upper lower v f = (f v).1 := rfl

@[simp] theorem pairFactorizationLower_apply (upper lower : FPrimeStrip V)
    (v : V) (f : (v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v) :
    pairFactorizationLower upper lower v f = (f v).2 := rfl

/-- The tuple homomorphism for a pair of families of homomorphisms. -/
def pairTupleHom {G : Type uG} [Group G] {upper lower : FPrimeStrip V}
    (gU : ∀ v : V, G →* upper.toDPrimeStrip.Pi v)
    (gL : ∀ v : V, G →* lower.toDPrimeStrip.Pi v) :
    G →* ((v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v) where
  toFun γ := fun v => (gU v γ, gL v γ)
  map_one' := by
    funext v
    change ((gU v) 1, (gL v) 1) =
      ((1, 1) : upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v)
    exact Prod.ext ((gU v).map_one) ((gL v).map_one)
  map_mul' γ δ := by
    funext v
    change ((gU v) (γ * δ), (gL v) (γ * δ)) =
      ((gU v) γ * (gU v) δ, (gL v) γ * (gL v) δ)
    exact Prod.ext ((gU v).map_mul γ δ) ((gL v).map_mul γ δ)

@[simp] theorem pairTupleHom_apply {G : Type uG} [Group G]
    {upper lower : FPrimeStrip V}
    (gU : ∀ v : V, G →* upper.toDPrimeStrip.Pi v)
    (gL : ∀ v : V, G →* lower.toDPrimeStrip.Pi v) (γ : G) (v : V) :
    pairTupleHom gU gL γ v = (gU v γ, gL v γ) := rfl

/-- Universality for strip pairs, upper side. -/
theorem pairFactorizationUpper_comp_pairTupleHom {G : Type uG} [Group G]
    {upper lower : FPrimeStrip V}
    (gU : ∀ v : V, G →* upper.toDPrimeStrip.Pi v)
    (gL : ∀ v : V, G →* lower.toDPrimeStrip.Pi v) (v : V) :
    (pairFactorizationUpper upper lower v).comp (pairTupleHom gU gL) = gU v := by
  ext γ
  rfl

/-- Universality for strip pairs, lower side. -/
theorem pairFactorizationLower_comp_pairTupleHom {G : Type uG} [Group G]
    {upper lower : FPrimeStrip V}
    (gU : ∀ v : V, G →* upper.toDPrimeStrip.Pi v)
    (gL : ∀ v : V, G →* lower.toDPrimeStrip.Pi v) (v : V) :
    (pairFactorizationLower upper lower v).comp (pairTupleHom gU gL) = gL v := by
  ext γ
  rfl

/-- The `sourceAction` shape of the SHE consumption slots on the upper strip
of a pair, for the canonical common group. -/
noncomputable def pairUnitsActionUpper (upper lower : FPrimeStrip V) (v : V) :
    ((v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v) →*
      MulAut ((upper.Mon v)ˣ) :=
  (upper.unitsAction v).comp (pairFactorizationUpper upper lower v)

/-- The `targetAction` shape of the SHE consumption slots on the lower strip
of a pair, for the canonical common group. -/
noncomputable def pairUnitsActionLower (upper lower : FPrimeStrip V) (v : V) :
    ((v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v) →*
      MulAut ((lower.Mon v)ˣ) :=
  (lower.unitsAction v).comp (pairFactorizationLower upper lower v)

@[simp] theorem pairUnitsActionUpper_apply (upper lower : FPrimeStrip V) (v : V)
    (f : (v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v)
    (u : (upper.Mon v)ˣ) :
    pairUnitsActionUpper upper lower v f u = upper.unitsAction v (f v).1 u := rfl

@[simp] theorem pairUnitsActionLower_apply (upper lower : FPrimeStrip V) (v : V)
    (f : (v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v)
    (u : (lower.Mon v)ˣ) :
    pairUnitsActionLower upper lower v f u = lower.unitsAction v (f v).2 u := rfl

end FPrimeStrip

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Unconditional factorization provider for the `G1-SRC-a` actions
sub-obligation (see the module docstring for the explicit faithfulness
boundary). -/
def kappaOrbitFactorizationProvider : Obligation :=
  { id := "IUT-II.kappa-orbit-factorization-provider"
    source :=
      "IUT II, Definition 4.9, (i), (ii); IUT II, Example 1.8, (iii), (iv)"
    status := VerificationStatus.provedKernel
    note :=
      "Unconditional provider: for every F-prime-strip the product of its " ++
        "local groups carries the canonical evaluation factorization; the " ++
        "κ-orbit datum of Definition 4.9, (i), is inhabited on it " ++
        "(universalKappaOrbitUnitsActionDatum), and the factorization of " ++
        "every other family g : forall v, G ->* Pi v is the composite of the " ++
        "canonical evaluation family with its tuple homomorphism " ++
        "(evaluationFactorization_comp_piTupleHom). Pair form: one common " ++
        "group for a strip pair with both evaluation factorizations and the " ++
        "ready-made sourceAction/targetAction composites " ++
        "(pairUnitsActionUpper/Lower) of the SHE consumption slots. Proved " ++
        "kernel only: the paper's identification of the acting group with " ++
        "Aut(‡A) ≅ Gw (split Frobenioid universal covering, 2l-torsion, " ++
        "splittings) and the group-theoretic algorithms of Example 1.8, " ++
        "(iii), (iv), are NOT constructed."
    dependsOn :=
      [ "IUT-II.kappa-orbit-units-action-supply", "IUT-I-II.prime-strip-core" ] }

end LeanFormal.IUT.Audit
