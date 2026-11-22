import tmp.sheaf.xif.paper.S1949NonarchimedeanLogShellActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceIndTopology
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import Iut.Foundations.SourceDefinition52IndSystem
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Topology.Algebra.Field

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S1962: R1 abstract `G_v`-action and the ind-topological `Ψ~`

Layer: **O** (original Theta-link / q-pilot), local nonarchimedean input to the
S1927 global packet.

## The paper object

IUT III, Definition 1.1, (i) (text l.1259-1351), associates to an
`F`-prime-strip `†F_v` the perfection

  `Ψ~_{†F_v} = (Ψ×_{†F_v})^pf`

of its unit monoid, with an algorithmically constructed ind-topological field
structure and a natural action of `G_v(†Π_v)`.  The pre-log-shell is the image
in `Ψ~` of the `G_v(†Π_v)`-invariant submonoid of `Ψ×`.  The paper's
construction is *functorial in the F-prime-strip* and is not the same thing as
the completed local field used in S1949 as a reduced model.

## What this file formalizes

1. **`Ψ~` as the actual unit perfection.**  For an actual finite place
   `v : FinitePrimePlace 2 7` we use

     `Ψ~ := SourceUnitPerfection (QPlace v)`,

   the genuine perfection of the actual integral units of the source algebraic
   closure (`FinitePlaceSourceAlgebraicUnitPerfection`).  It is not an
   arbitrary carrier: every element is a fraction of actual integral units.

2. **The actual `G_v`-action.**  The actual local Galois group

     `G_v := SourceAlgebraicClosure (QPlace v) ≃ₐ[NormalizedCompletion (QPlace v)]
              SourceAlgebraicClosure (QPlace v)`

   acts on `Ψ~` through `sourceUnitPerfectionGaloisAction`.  We prove that this
   action preserves the transported field multiplication
   (`psiTilde_smul_mul`), and that its fixed points are exactly the embedded
   completion (`psiTilde_fixed_iff`).  No invariant submonoid is postulated.

3. **The ind-topological presentation.**  `sourceUnitPerfectionIndTopology` is
   the actual final topology of the genuine finite local subfields, and
   `sourceUnitPerfectionIndHomeomorph` identifies it with the actual algebraic
   closure carrying its ind field topology.  This is the ind-topological
   *space* underlying `Ψ~`.

4. **An actual local F-prime-strip with `G_v`-action.**  On the source finite
   stage system of `Iut.Foundations.SourceDefinition52IndSystem`, the actual
   nonzero integral monoid and the actual Krull action give a concrete
   `FPrimeStrip` (`localFPrimeStrip`) together with an
   `AbstractGvActionOnFPrimeStrip` (`localAbstractGvAction`).  This is a
   local actual model of the abstract action on a prime strip.

5. **The actual invariant units are not faked.**  S1949 proves that the
   `G_v`-invariant units inside `O_v^×` are *all* of `O_v^×`
   (`galoisFixedCompletionUnits_eq_top`, reused below as
   `actualCompletionInvariantUnits_eq_top`).  The invariant submodule of `Ψ~`
   is the fixed submodule of the actual action, not an input slot.

## Exact first missing (as required by S1962)

The algebraic action and the ind-topological *space* are actual, but the
paper's **ind-topological field structure** and the **joint continuity of the
action on the limit** are not established:

* `R1FirstMissing v` is the proposition that the transported field structure on
  `Ψ~` together with `sourceUnitPerfectionIndTopology` is a topological
  division ring.  The ind topology is a final topology of finite stages; its
  compatibility with the field operations is not automatic and is not in the
  tree.  This is the first missing `Ψ~` structure, not a fake invariant
  submonoid.

* `R1JointContinuousActionMissing v` is the proposition that the action map
  `G_v × Ψ~ → Ψ~` is jointly continuous for the ind topology.  Stagewise
  continuity is proved in `Iut.Foundations.SourceDefinition52LocalJointContinuity`
  (and is reused through the actual stage action), but that file explicitly
  records that joint continuity on the single limit carrier requires a
  separate continuity-with-parameters theorem.  That theorem is the exact
  second missing.

* `R1AbstractActionOnDaggerFMissing F v` is the statement that the abstract
  prime strip `F` admits a `G`-action on its value monoid compatible with the
  `Pi`-action.  For the concrete local strip above it is inhabited; for the
  paper's abstract `†F` it is not constructed.  The paper's `†F` carrier is an
  explicit source input (`SourceTheaterRealization` proves it is not
  determined by Definition 3.1 data alone), so this is a genuine comparison
  gap, not a vacuous `Nonempty` gate.

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type or arbitrary inhabitant is
used.  The only `PUnit` occurrence is the one-point index of the local
F-prime-strip; it is not an invariant submonoid or a witness for a missing
field.

## Source locations

* IUT III, Definition 1.1, (i), text l.1259-1351 (Ψ~, ind-topological field,
  `G_v(†Π_v)`-invariants, pre-log-shell/log-shell).
* IUT III, Definition 1.1, (iii), l.1503-1521 (`log(†F_v) = Ψ~` with its
  natural `G_v(†Π_v)`-action).
* IUT II, Corollary 4.6 (the functorial construction of `Ψcns(†F)`).
* Upstream actual sources: `FinitePlaceSourceAlgebraicUnitPerfection`,
  `FinitePlaceSourceIndTopology`, `SourceDefinition52IndSystem`,
  `SourceDefinition52LocalJointContinuity`.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1949NonarchimedeanLogShellActual

namespace LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual

/-! ## 0. Actual place, group, and `Ψ~` -/

/-- The actual rational finite place underlying a one-column place. -/
abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace Rat :=
  finitePrimePlaceToQ v

/-- The actual local Galois group `G_v` used by the source model. -/
abbrev PsiTildeGroup (v : FinitePrimePlace 2 7) : Type :=
  SourceAlgebraicClosure (QPlace v) ≃ₐ[NormalizedCompletion (QPlace v)]
    SourceAlgebraicClosure (QPlace v)

/-- The actual unit perfection `Ψ~ = (Ψ×)^pf` of the source local field. -/
abbrev PsiTilde (v : FinitePrimePlace 2 7) : Type :=
  SourceUnitPerfection (QPlace v)

/-- The field structure on `Ψ~` transported from the actual algebraic closure
by the actual logarithmic identification.  This is the paper's field
structure on the perfection, before any topology is imposed. -/
@[reducible] noncomputable def psiTildeField (v : FinitePrimePlace 2 7) :
    Field (PsiTilde v) :=
  (sourceUnitPerfectionEquiv (QPlace v)).toEquiv.field

/-- The actual `G_v`-action on `Ψ~`, transported from the actual local Galois
action on the algebraic closure. -/
abbrev psiTildeAction (v : FinitePrimePlace 2 7) :
    MulAction (PsiTildeGroup v) (PsiTilde v) :=
  sourceUnitPerfectionGaloisAction (QPlace v)

/-- The actual ind-topology on `Ψ~` (final topology of the genuine finite local
subfields). -/
abbrev psiTildeIndTopology (v : FinitePrimePlace 2 7) :
    TopologicalSpace (PsiTilde v) :=
  sourceUnitPerfectionIndTopology (QPlace v)

/-! ## 1. The algebraic action is an action by field automorphisms -/

/-- The actual logarithmic identification sends the transported multiplication
on `Ψ~` to the multiplication of the algebraic closure. -/
theorem psiTilde_field_mul_apply (v : FinitePrimePlace 2 7)
    (x y : PsiTilde v) :
    letI := psiTildeField v
    sourceUnitPerfectionEquiv (QPlace v) (x * y) =
      sourceUnitPerfectionEquiv (QPlace v) x *
        sourceUnitPerfectionEquiv (QPlace v) y := by
  letI := psiTildeField v
  change (sourceUnitPerfectionEquiv (QPlace v))
    ((sourceUnitPerfectionEquiv (QPlace v)).symm
      ((sourceUnitPerfectionEquiv (QPlace v)) x *
        (sourceUnitPerfectionEquiv (QPlace v)) y)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- **The actual `G_v`-action preserves the field multiplication.**  Thus the
transported field structure on `Ψ~` is genuinely equivariant under the actual
local Galois action, not merely a linear action on the underlying vector
space. -/
theorem psiTilde_smul_mul (v : FinitePrimePlace 2 7)
    (σ : PsiTildeGroup v) (x y : PsiTilde v) :
    letI := psiTildeField v
    letI := psiTildeAction v
    σ • (x * y) = (σ • x) * (σ • y) := by
  letI := psiTildeField v
  letI := psiTildeAction v
  refine (sourceUnitPerfectionEquiv (QPlace v)).injective ?_
  rw [sourceUnitPerfectionEquiv_galois_smul]
  rw [psiTilde_field_mul_apply v x y]
  conv_rhs => rw [psiTilde_field_mul_apply v (σ • x) (σ • y)]
  rw [sourceUnitPerfectionEquiv_galois_smul,
    sourceUnitPerfectionEquiv_galois_smul]
  exact map_mul σ _ _

/-- The actual `G_v`-action is compatible with the ind-topological
identification `Ψ~ ≃ₜ SourceAlgebraicClosure` (the paper's
`G_v(†Π_v)`-action on the ind-topological field). -/
theorem psiTildeIndHomeomorph_galois_smul (v : FinitePrimePlace 2 7)
    (σ : PsiTildeGroup v) (x : PsiTilde v) :
    letI := psiTildeIndTopology v
    letI := sourceAlgebraicFieldIndTopology (QPlace v)
    letI := psiTildeAction v
    sourceUnitPerfectionIndHomeomorph (QPlace v) (σ • x) =
      σ (sourceUnitPerfectionIndHomeomorph (QPlace v) x) :=
  sourceUnitPerfectionIndHomeomorph_galois_smul (QPlace v) σ x

/-! ## 2. The fixed points of the actual action are the completion -/

/-- The completion embedded in `Ψ~` as a `Rat`-submodule (via the actual
logarithmic identification).  This is the fixed submodule of the actual
`G_v`-action, not an input slot. -/
noncomputable def psiTildeCompletionSubmodule (v : FinitePrimePlace 2 7) :
    Submodule Rat (PsiTilde v) :=
  Submodule.map (sourceUnitPerfectionEquiv (QPlace v)).symm.toLinearMap
    ((Algebra.linearMap (NormalizedCompletion (QPlace v))
      (SourceAlgebraicClosure (QPlace v))).range.restrictScalars Rat)

/-- Membership in the completion submodule is exactly membership in the image
of the actual completion. -/
theorem mem_psiTildeCompletionSubmodule_iff (v : FinitePrimePlace 2 7)
    (x : PsiTilde v) :
    x ∈ psiTildeCompletionSubmodule v ↔
      sourceUnitPerfectionEquiv (QPlace v) x ∈
        Set.range (algebraMap (NormalizedCompletion (QPlace v))
          (SourceAlgebraicClosure (QPlace v))) := by
  rw [psiTildeCompletionSubmodule, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hy
    simpa using hy
  · intro hx
    refine ⟨sourceUnitPerfectionEquiv (QPlace v) x, ?_, ?_⟩
    · rw [Submodule.restrictScalars_mem, LinearMap.mem_range]
      simpa [Algebra.linearMap] using hx
    · exact (sourceUnitPerfectionEquiv (QPlace v)).symm_apply_apply x

/-- **The fixed points of the actual `G_v`-action on `Ψ~` are exactly the
embedded completion.**  This is the actual fixed-module theorem, not a choice
of invariant submonoid. -/
theorem psiTilde_fixed_iff (v : FinitePrimePlace 2 7) (x : PsiTilde v) :
    (letI := psiTildeAction v
     ∀ σ : PsiTildeGroup v, σ • x = x) ↔
      x ∈ psiTildeCompletionSubmodule v := by
  rw [mem_psiTildeCompletionSubmodule_iff]
  exact sourceUnitPerfection_fixed_iff (QPlace v) x

/-! ## 3. The actual invariant units inside `O_v^×` -/

/-- **No fake nontrivial invariant submonoid**: S1949 proves that the actual
`G_v`-invariant subgroup of the completed units is the whole of `O_v^×`.
This theorem is reused, not restated as a definition. -/
theorem actualCompletionInvariantUnits_eq_top (v : FinitePrimePlace 2 7) :
    galoisFixedCompletionUnits v = ⊤ :=
  galoisFixedCompletionUnits_eq_top v

/-- Definitional unfolding of the fixed submodule: it is the completion
submodule, not an independently chosen invariant. -/
theorem psiTilde_fixed_submodule_eq_completion (v : FinitePrimePlace 2 7) :
    psiTildeCompletionSubmodule v =
      Submodule.map (sourceUnitPerfectionEquiv (QPlace v)).symm.toLinearMap
        ((Algebra.linearMap (NormalizedCompletion (QPlace v))
          (SourceAlgebraicClosure (QPlace v))).range.restrictScalars Rat) :=
  rfl

/-! ## 4. An actual local F-prime-strip with `G_v`-action -/

/-- The actual local base field of the finite-stage source system. -/
abbrev LocalBase (v : FinitePrimePlace 2 7) : Type :=
  Iut.SourceFinitePlaceReconstruction.Base (QPlace v)

/-- The actual local algebraic closure of the finite-stage source system. -/
abbrev LocalClosure (v : FinitePrimePlace 2 7) : Type :=
  Iut.SourceFinitePlaceReconstruction.Closure (QPlace v)

/-- The actual local absolute Galois group of the finite-stage source system. -/
abbrev LocalGalois (v : FinitePrimePlace 2 7) : Type :=
  LocalClosure v ≃ₐ[LocalBase v] LocalClosure v

/-- The actual nonzero integral monoid of the finite-stage source system. -/
abbrev LocalIndMonoid (v : FinitePrimePlace 2 7) : Type :=
  Iut.SourceFinitePlaceReconstruction.IndIntegralMonoid (QPlace v)

/-- The actual norm-log degree on the nonzero integral monoid. -/
noncomputable def localNormLog (v : FinitePrimePlace 2 7) :
    LocalIndMonoid v →* Multiplicative Real where
  toFun x := Multiplicative.ofAdd
    (Real.log ‖Iut.SourceFinitePlaceReconstruction.carrierMulEquivAlgebraicClosure
      (QPlace v) x.1‖)
  map_one' := by
    apply Multiplicative.ext
    simp
  map_mul' x y := by
    apply Multiplicative.ext
    change Real.log ‖Iut.SourceFinitePlaceReconstruction.carrierMulEquivAlgebraicClosure
        (QPlace v) (x * y).1‖ =
      Real.log ‖Iut.SourceFinitePlaceReconstruction.carrierMulEquivAlgebraicClosure
        (QPlace v) x.1‖ +
      Real.log ‖Iut.SourceFinitePlaceReconstruction.carrierMulEquivAlgebraicClosure
        (QPlace v) y.1‖
    have hx : Iut.SourceFinitePlaceReconstruction.carrierMulEquivAlgebraicClosure
        (QPlace v) x.1 ≠ 0 := by
      intro h
      exact x.2.2 h
    have hy : Iut.SourceFinitePlaceReconstruction.carrierMulEquivAlgebraicClosure
        (QPlace v) y.1 ≠ 0 := by
      intro h
      exact y.2.2 h
    rw [Submonoid.coe_mul, map_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]

/-- The actual local `F`-prime-strip built from the genuine finite-stage ind
system.  `PUnit` is only the one-point place index. -/
noncomputable def localFPrimeStrip (v : FinitePrimePlace 2 7) :
    FPrimeStrip.{0, 0, 0} PUnit where
  Pi := fun _ => LocalGalois v
  groupPi := fun _ => inferInstance
  G := fun _ => LocalGalois v
  groupG := fun _ => inferInstance
  proj := fun _ => MonoidHom.id _
  proj_surjective := fun _ => Function.surjective_id
  Mon := fun _ => LocalIndMonoid v
  commMonoidMon := fun _ => inferInstance
  action := fun _ =>
    Iut.SourceFinitePlaceReconstruction.indGaloisAction (QPlace v)
  degree := fun _ => localNormLog v

/-- A `G`-action on an `F`-prime-strip compatible with its `Pi`-action.  This is
the abstract form of the paper's `G_v(†Π_v)`-action on `†F_v` at one place. -/
structure AbstractGvActionOnFPrimeStrip
    {V : Type} (F : FPrimeStrip.{0, 0, 0} V) (v : V) where
  /-- the abstract `G`-action on the value monoid at `v` -/
  action : F.G v →* MulAut (F.Mon v)
  /-- compatibility with the defining `Pi`-action of the prime strip -/
  compatible_proj : ∀ g : F.Pi v, action (F.proj v g) = F.action v g

/-- The actual local prime strip has the genuine Krull action on its value
monoid, and `Pi = G` with identity projection, so the abstract action interface
is inhabited by actual arithmetic data. -/
noncomputable def localAbstractGvAction (v : FinitePrimePlace 2 7) :
    AbstractGvActionOnFPrimeStrip (localFPrimeStrip v) PUnit.unit where
  action := (localFPrimeStrip v).action PUnit.unit
  compatible_proj := fun _ => rfl

/-- The action field of the actual local model is the actual Krull action. -/
theorem localAbstractGvAction_action (v : FinitePrimePlace 2 7) :
    (localAbstractGvAction v).action =
      (localFPrimeStrip v).action PUnit.unit := rfl

/-! ## 5. The exact missing statements -/

/-- **R1 first missing (Ψ~ structure).**  The transported field structure on
`Ψ~` together with the actual ind-topology is a topological division ring.
This is the paper's ind-topological field structure at the reduced carrier
`Ψ~ = (Ψ×)^pf`; it is not automatic from the final-topology definition. -/
def R1FirstMissing (v : FinitePrimePlace 2 7) : Prop :=
  letI := psiTildeField v
  letI := psiTildeIndTopology v
  IsTopologicalDivisionRing (PsiTilde v)

/-- **R1 joint-continuity missing.**  The actual action map `G_v × Ψ~ → Ψ~` is
jointly continuous for the ind topology.  Stagewise continuity is available in
`SourceDefinition52LocalJointContinuity`; the limit statement is the named
missing continuity-with-parameters theorem. -/
def R1JointContinuousActionMissing (v : FinitePrimePlace 2 7) : Prop :=
  letI := psiTildeAction v
  letI := psiTildeIndTopology v
  Continuous fun p : PsiTildeGroup v × PsiTilde v => p.1 • p.2

/-- **R1 abstract `†F_v`-action missing.**  For a general abstract
`F`-prime-strip there is no construction, in the tree, of a `G`-action on the
value monoid compatible with the defining `Pi`-action.  For the concrete local
strip this type is inhabited (`localAbstractGvAction`); the paper's abstract
`†F` is an explicit source input. -/
def R1AbstractActionOnDaggerF
    {V : Type} (F : FPrimeStrip.{0, 0, 0} V) (v : V) : Type :=
  AbstractGvActionOnFPrimeStrip F v

/-- The missing abstract-action proposition for the paper's `†F_v`. -/
def R1AbstractActionOnDaggerFMissing
    {V : Type} (F : FPrimeStrip.{0, 0, 0} V) (v : V) : Prop :=
  Nonempty (R1AbstractActionOnDaggerF F v)

/-- The local actual model proves that the abstract-action interface is not
vacuous: it is inhabited by the actual Krull action on the actual ind integral
monoid.  This does not identify the paper's abstract `†F` with the local model. -/
theorem localAbstractGvAction_inhabited (v : FinitePrimePlace 2 7) :
    R1AbstractActionOnDaggerFMissing (localFPrimeStrip v) PUnit.unit :=
  ⟨localAbstractGvAction v⟩

/-- The fixed submodule of the actual action is the completion submodule.
This is the conclusion used by the consumers: the invariant part of `Ψ~` is
computed, not declared. -/
theorem actualAction_fixed_eq_completion (v : FinitePrimePlace 2 7) :
    (letI := psiTildeAction v
     {x : PsiTilde v | ∀ σ : PsiTildeGroup v, σ • x = x}) =
      (psiTildeCompletionSubmodule v : Set (PsiTilde v)) := by
  ext x
  exact psiTilde_fixed_iff v x

/-! ## 6. Axiom probes -/

#print axioms psiTilde_smul_mul
#print axioms psiTilde_fixed_iff
#print axioms actualAction_fixed_eq_completion
#print axioms actualCompletionInvariantUnits_eq_top
#print axioms localAbstractGvAction_inhabited

end LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual

end
