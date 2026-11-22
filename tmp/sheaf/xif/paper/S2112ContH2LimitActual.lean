import tmp.sheaf.xif.paper.S2036ActualPsiCnsM234Actual
import Mathlib.Topology.LocallyConstant.Basic

/-!
# S2112: inverse limits of continuous H² and the degree-two limit exchange

Layer: **O**.  Consumers: S2091 (the named proposition PsiCnsH2LimitComparison,
where the comparison is stated on the actual cyclotome), and through it S2036
(M3, PsiCnsH2Normalization).

## What is proved here (unconditional; no sorry, no new axioms)

1. **First sublemma.**  A continuous map into a discrete space is locally
   constant (`continuous_isLocallyConstant_of_discrete`), and on a compact
   domain it has finite image (`finite_range_of_compact_of_discrete`).  These
   are packaged versions of Mathlib's `IsLocallyConstant.iff_continuous` and
   `IsLocallyConstant.range_finite`, so no topological API is missing for the
   statement in this form; the finite-quotient refinement for profinite `G`
   is a separate step and is not needed for the limit exchange below.

2. **The abstract inverse limit.**  For groups `B n` and transition maps
   `q n : B (n+1) →* B n`, `limSubgroup B q ≤ ∏ n, B n` is the inverse
   limit; `continuous_lim_iff` states that a map into it is continuous iff
   all its coordinates are (initial topology).

3. **Coefficient system and limit action.**  Given finite discrete coefficient
   groups `A n` with transition maps `proj n`, compatible continuous actions
   `actn n` of a topological group `G`, the levelwise action on the inverse
   limit is a continuous action `limitAction`.

4. **Cochain exchange in degrees one and two.**  Continuous 1- and 2-cochains
   with values in the inverse limit are multiplicatively equivalent to the
   inverse limits of the level cochain groups (`oneCochainEquiv`,
   `twoCochainEquiv`); the second differential commutes with level
   projections (`deltaTwo_coord`).

5. **Cocycle and Z² exchange (the requested "at least" target), unconditional.**
   A 2-cochain into the limit is a 2-cocycle iff all its level projections are
   (`mem_twoCocycle_iff_levels`), and

     `twoCocycleExchange : Z²_cont(G, lim A) ≃* lim_n Z²_cont(G, A_n)`,

   the right-hand side being the subgroup `twoCocycleLimFamily` of compatible
   families of level cocycles.  Neither finiteness nor any lim¹ input is used.

6. **The degree-two comparison.**  Level projections of H² give maps
   `h2Proj n : H²(G, A(n+1)) →* H²(G, A n)`, the limit `LimH2`, and the
   comparison `h2Comparison : H²_cont(G, lim A) →* lim_n H²_cont(G, A_n)`.

7. **The exact remaining gap.**  `h2Comparison_injective_iff` proves that the
   comparison is injective *iff* the coboundary lift (`CoboundaryLift`)
   holds: every 2-cocycle of the limit whose level projections are all
   coboundaries is itself a coboundary.  This is precisely the lim¹-vanishing
   `lim¹_n H¹(G, A_n) = 0`, which holds when the level `H¹` are finite and
   the system satisfies Mittag-Leffler (in the arithmetic application
   `H¹(G_v, μ_n) ≅ ℤ/n`).  It is a homological input, not a topological API
   gap; the port's `Brauer/H2ZHat.lean` cites the same input.  Surjectivity of
   the comparison is provable by the usual lifting of level representatives but
   is *not* formalized in this file, so the full degree-two exchange is not
   claimed here; `coboundaryLift_of_bijective` records the converse direction.

## Not run

Full lake build of the project, comparator, and independent source-semantics
review are not part of this file.  The only axioms used are the three standard
ones, checked by the `#print axioms` probes at the end.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false

universe u

namespace LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual

open Iut
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual

/-! ## 1. Continuous maps to discrete spaces are locally constant -/

section LocallyConstant

variable {X : Type u} {Y : Type u}

theorem continuous_isLocallyConstant_of_discrete [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] {f : X → Y} (hf : Continuous f) : IsLocallyConstant f :=
  (IsLocallyConstant.iff_continuous f).2 hf

/-- The statement requested as the first sublemma: a continuous map from a
compact totally disconnected space to a discrete space is locally constant. -/
theorem compact_totallyDisconnected_isLocallyConstant [TopologicalSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [TopologicalSpace Y] [DiscreteTopology Y] {f : X → Y}
    (hf : Continuous f) : IsLocallyConstant f :=
  continuous_isLocallyConstant_of_discrete hf

theorem finite_range_of_compact_of_discrete [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] {f : X → Y} (hf : Continuous f) :
    (Set.range f).Finite :=
  (continuous_isLocallyConstant_of_discrete hf).range_finite

end LocallyConstant

/-! ## 2. The abstract inverse limit of a sequence of groups -/

section LimitGroup

variable (B : ℕ → Type u) [∀ n, CommGroup (B n)] (q : ∀ n, B (n+1) →* B n)

def limSubgroup : Subgroup (∀ n, B n) where
  carrier := {x | ∀ n, q n (x (n+1)) = x n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hx hy n
    simp [hx n, hy n]
  inv_mem' := by
    intro x hx n
    simp [hx n]

abbrev Lim : Type u := limSubgroup B q

theorem mem_lim_iff {x : ∀ n, B n} : x ∈ limSubgroup B q ↔ ∀ n, q n (x (n+1)) = x n :=
  Iff.rfl

@[ext]
theorem Lim.ext {x y : Lim B q} (h : ∀ n, (x : ∀ k, B k) n = (y : ∀ k, B k) n) : x = y :=
  Subtype.ext (funext h)

end LimitGroup

section LimitGroupTop

variable {B : ℕ → Type u} [∀ n, CommGroup (B n)] [∀ n, TopologicalSpace (B n)]
  {q : ∀ n, B (n+1) →* B n}

theorem continuous_lim_iff {X : Type u} [TopologicalSpace X] (f : X → Lim B q) :
    Continuous f ↔ ∀ n, Continuous fun x => (f x : ∀ k, B k) n := by
  constructor
  · intro hf n
    exact (continuous_apply n).comp (continuous_subtype_val.comp hf)
  · intro h
    have hprod : Continuous fun x => (f x : ∀ k, B k) := continuous_pi_iff.mpr h
    have hsub : Continuous fun x => (⟨(f x : ∀ k, B k), (f x).2⟩ : Lim B q) :=
      hprod.subtype_mk fun x => (f x).2
    simpa using hsub

end LimitGroupTop

/-! ## 3. Coefficient systems and the limit action -/

section CoeffSystem

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (A : ℕ → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)

abbrev LimCoeff : Type u := Lim A proj

variable (actn : ∀ n, Iut.ContinuousGroupAction G (A n))
variable (compat : ∀ n (g : G) (x : A (n+1)),
  proj n ((actn (n+1)).act g x) = (actn n).act g (proj n x))

def limActFun (g : G) (x : LimCoeff A proj) : LimCoeff A proj :=
  ⟨fun n => (actn n).act g ((x : ∀ k, A k) n), by
    intro n
    rw [compat n g ((x : ∀ k, A k) (n+1)), x.2 n]⟩

@[simp]
theorem limActFun_apply (g : G) (x : LimCoeff A proj) (n : ℕ) :
    ((limActFun A proj actn compat g x : ∀ k, A k) n) =
      (actn n).act g ((x : ∀ k, A k) n) :=
  rfl

def limAut (g : G) : MulAut (LimCoeff A proj) where
  toFun := limActFun A proj actn compat g
  invFun := limActFun A proj actn compat g⁻¹
  left_inv x := by
    apply Lim.ext
    intro n
    rw [limActFun_apply, limActFun_apply, ← ContinuousGroupAction.act_mul_group,
      inv_mul_cancel, ContinuousGroupAction.act_one_group]
  right_inv x := by
    apply Lim.ext
    intro n
    rw [limActFun_apply, limActFun_apply, ← ContinuousGroupAction.act_mul_group,
      mul_inv_cancel, ContinuousGroupAction.act_one_group]
  map_mul' x y := by
    apply Lim.ext
    intro n
    simp [limActFun, ContinuousGroupAction.act_mul]

@[simp]
theorem limAut_apply (g : G) (x : LimCoeff A proj) (n : ℕ) :
    (((limAut A proj actn compat g) x : ∀ k, A k) n) =
      (actn n).act g ((x : ∀ k, A k) n) :=
  rfl

def limAutHom : G →* MulAut (LimCoeff A proj) where
  toFun := limAut A proj actn compat
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    apply Lim.ext
    intro n
    simp [limAut]
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    apply Lim.ext
    intro n
    simp [limAut, ContinuousGroupAction.act_mul_group]

def limitAction : Iut.ContinuousGroupAction G (LimCoeff A proj) where
  automorphism := limAutHom A proj actn compat
  continuous_action := by
    rw [continuous_lim_iff]
    intro n
    have hc : Continuous fun p : G × LimCoeff A proj =>
        (p.1, ((p.2 : ∀ k, A k) n)) :=
      continuous_fst.prodMk
        ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))
    have h1 : Continuous fun p : G × LimCoeff A proj =>
        (actn n).act p.1 ((p.2 : ∀ k, A k) n) :=
      (actn n).continuous_action.comp hc
    refine h1.congr ?_
    intro p
    rfl

@[simp]
theorem limitAction_act_apply (g : G) (x : LimCoeff A proj) (n : ℕ) :
    (((limitAction A proj actn compat).act g x : ∀ k, A k) n) =
      (actn n).act g ((x : ∀ k, A k) n) :=
  rfl

end CoeffSystem

/-! ## 4. Cochain exchange in degrees one and two -/

section Cochains

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : ℕ → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)
variable (actn : ∀ n, Iut.ContinuousGroupAction G (A n))
variable (compat : ∀ n (g : G) (x : A (n+1)),
  proj n ((actn (n+1)).act g x) = (actn n).act g (proj n x))

/-- The level-n projection of continuous 1-cochains. -/
def oneCochainLevel (n : ℕ) :
    ContinuousOneCochain (G := G) (A := LimCoeff A proj) →*
      ContinuousOneCochain (G := G) (A := A n) where
  toFun c := ⟨fun x => ((c.1 x : LimCoeff A proj) : ∀ m, A m) n,
    (continuous_apply n).comp (continuous_subtype_val.comp c.2)⟩
  map_one' := by
    apply Subtype.ext
    funext x
    rfl
  map_mul' c d := by
    apply Subtype.ext
    funext x
    rfl

@[simp] theorem oneCochainLevel_apply (n : ℕ)
    (c : ContinuousOneCochain (G := G) (A := LimCoeff A proj)) (x : G) :
    (↑(oneCochainLevel A proj n c) : G → A n) x =
      ((c.1 x : LimCoeff A proj) : ∀ m, A m) n := rfl

/-- The transition map of continuous 1-cochains. -/
def oneCochainProj (n : ℕ) :
    ContinuousOneCochain (G := G) (A := A (n+1)) →*
      ContinuousOneCochain (G := G) (A := A n) where
  toFun c := ⟨fun x => proj n (c.1 x),
    (continuous_of_discreteTopology (f := proj n)).comp c.2⟩
  map_one' := by
    apply Subtype.ext
    funext x
    simp
  map_mul' c d := by
    apply Subtype.ext
    funext x
    simp

@[simp] theorem oneCochainProj_apply (n : ℕ)
    (c : ContinuousOneCochain (G := G) (A := A (n+1))) (x : G) :
    (↑(oneCochainProj A proj n c) : G → A n) x = proj n (c.1 x) := rfl

/-- The level-n projection of continuous 2-cochains. -/
def twoCochainLevel (n : ℕ) :
    ContinuousTwoCochain (G := G) (A := LimCoeff A proj) →*
      ContinuousTwoCochain (G := G) (A := A n) where
  toFun c := ⟨fun x => ((c.1 x : LimCoeff A proj) : ∀ m, A m) n,
    (continuous_apply n).comp (continuous_subtype_val.comp c.2)⟩
  map_one' := by
    apply ContinuousTwoCochain.ext
    intro x y
    rfl
  map_mul' c d := by
    apply ContinuousTwoCochain.ext
    intro x y
    rfl

@[simp] theorem twoCochainLevel_apply (n : ℕ)
    (c : ContinuousTwoCochain (G := G) (A := LimCoeff A proj)) (x : G × G) :
    (↑(twoCochainLevel A proj n c) : G × G → A n) x =
      ((c.1 x : LimCoeff A proj) : ∀ m, A m) n := rfl

/-- The transition map of continuous 2-cochains. -/
def twoCochainProj (n : ℕ) :
    ContinuousTwoCochain (G := G) (A := A (n+1)) →*
      ContinuousTwoCochain (G := G) (A := A n) where
  toFun c := ⟨fun x => proj n (c.1 x),
    (continuous_of_discreteTopology (f := proj n)).comp c.2⟩
  map_one' := by
    apply ContinuousTwoCochain.ext
    intro x y
    simp
  map_mul' c d := by
    apply ContinuousTwoCochain.ext
    intro x y
    simp

@[simp] theorem twoCochainProj_coe_apply (n : ℕ)
    (c : ContinuousTwoCochain (G := G) (A := A (n+1))) (x : G × G) :
    (↑(twoCochainProj A proj n c) : G × G → A n) x = proj n (c.1 x) := rfl

/-- The inverse limit of the level 1-cochain groups. -/
def oneCochainLim : Subgroup (∀ n, ContinuousOneCochain (G := G) (A := A n)) :=
  limSubgroup (fun n => ContinuousOneCochain (G := G) (A := A n))
    (fun n => oneCochainProj A proj n)

/-- The inverse limit of the level 2-cochain groups. -/
def twoCochainLim : Subgroup (∀ n, ContinuousTwoCochain (G := G) (A := A n)) :=
  limSubgroup (fun n => ContinuousTwoCochain (G := G) (A := A n))
    (fun n => twoCochainProj A proj n)

/-- **Cochain exchange in degree one.** -/
def oneCochainEquiv (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : ℕ → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
    (proj : ∀ n, A (n+1) →* A n) :
    ContinuousOneCochain (G := G) (A := LimCoeff A proj) ≃* oneCochainLim (G := G) A proj where
  toFun c := ⟨fun n => oneCochainLevel A proj n c, by
    intro n
    apply Subtype.ext
    funext x
    exact (c.1 x).2 n⟩
  invFun c :=
    let F : G → LimCoeff A proj := fun x => ⟨fun n => (c.1 n).1 x, by
      intro n
      have h := congrArg (fun f : ContinuousOneCochain (G := G) (A := A n) => f.1 x) (c.2 n)
      simpa [oneCochainProj] using h⟩
    ⟨F, by
      change Continuous F
      exact (continuous_lim_iff F).mpr (fun n => (c.1 n).2)⟩
  left_inv c := by
    apply Subtype.ext
    funext x
    rfl
  right_inv c := by
    apply Subtype.ext
    funext n
    apply Subtype.ext
    funext x
    rfl
  map_mul' c d := by
    apply Subtype.ext
    funext n
    apply Subtype.ext
    funext x
    rfl

/-- **Cochain exchange in degree two.** -/
def twoCochainEquiv (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : ℕ → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
    (proj : ∀ n, A (n+1) →* A n) :
    ContinuousTwoCochain (G := G) (A := LimCoeff A proj) ≃* twoCochainLim (G := G) A proj where
  toFun c := ⟨fun n => twoCochainLevel A proj n c, by
    intro n
    apply ContinuousTwoCochain.ext
    intro x y
    exact (c.1 (x, y)).2 n⟩
  invFun c :=
    let F : G × G → LimCoeff A proj := fun x => ⟨fun n => (c.1 n).1 x, by
      intro n
      have h := congrArg (fun f : ContinuousTwoCochain (G := G) (A := A n) => f.1 x) (c.2 n)
      simpa [twoCochainProj] using h⟩
    ⟨F, by
      change Continuous F
      exact (continuous_lim_iff F).mpr (fun n => (c.1 n).2)⟩
  left_inv c := by
    apply ContinuousTwoCochain.ext
    intro x y
    rfl
  right_inv c := by
    apply Subtype.ext
    funext n
    apply ContinuousTwoCochain.ext
    intro x y
    rfl
  map_mul' c d := by
    apply Subtype.ext
    funext n
    apply ContinuousTwoCochain.ext
    intro x y
    rfl

/-- The second differential commutes with the level projection of 2-cochains. -/
theorem deltaTwo_coord (c : ContinuousTwoCochain (G := G) (A := LimCoeff A proj))
    (g h k : G) (n : ℕ) :
    ((deltaTwo (limitAction A proj actn compat) c).1 (g, h, k) : ∀ m, A m) n =
      (deltaTwo (actn n) (twoCochainLevel A proj n c)).1 (g, h, k) :=
  rfl

/- The level-n projection of a 2-cocycle is a 2-cocycle. -/
include compat in
theorem twoCochainProj_mem_twoCocycle {n : ℕ}
    {c : ContinuousTwoCochain (G := G) (A := A (n+1))}
    (hc : c ∈ twoCocycleSubgroup (action := actn (n+1))) :
    twoCochainProj A proj n c ∈ twoCocycleSubgroup (action := actn n) := by
  rw [mem_twoCocycle_iff] at hc ⊢
  intro g h k
  have h2 := congrArg (proj n) (hc g h k)
  rw [map_mul, map_mul] at h2
  rw [compat n g (c.1 (h, k))] at h2
  simpa only [twoCochainProj_coe_apply] using h2

/-- **Cocycle exchange**: a continuous 2-cochain into the inverse limit is a
2-cocycle if and only if all its level projections are 2-cocycles. -/
theorem mem_twoCocycle_iff_levels
    (c : ContinuousTwoCochain (G := G) (A := LimCoeff A proj)) :
    c ∈ twoCocycleSubgroup (action := limitAction A proj actn compat) ↔
      ∀ n, twoCochainLevel A proj n c ∈ twoCocycleSubgroup (action := actn n) := by
  rw [mem_twoCocycle_iff]
  constructor
  · intro hc n
    rw [mem_twoCocycle_iff]
    intro g h k
    have h2 := congrArg (fun z : LimCoeff A proj => (z : ∀ m, A m) n) (hc g h k)
    simpa [twoCochainLevel_apply, limitAction_act_apply, Pi.mul_apply, Pi.inv_apply] using h2
  · intro hc g h k
    apply Lim.ext
    intro n
    have hn : twoCochainLevel A proj n c ∈ twoCocycleSubgroup (action := actn n) := hc n
    rw [mem_twoCocycle_iff] at hn
    have hnk := hn g h k
    simpa [twoCochainLevel_apply, limitAction_act_apply, Pi.mul_apply, Pi.inv_apply] using hnk

/-- The inverse limit of the level 2-cocycle groups, presented inside the
inverse limit of the cochain groups. -/
def twoCocycleLimFamily : Subgroup (∀ n, ContinuousTwoCochain (G := G) (A := A n)) where
  carrier := {c | (∀ n, twoCochainProj A proj n (c (n+1)) = c n) ∧
    ∀ n, c n ∈ twoCocycleSubgroup (action := actn n)}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro n
      simp
    · intro n
      exact (twoCocycleSubgroup (action := actn n)).one_mem
  mul_mem' hx hy := by
    refine ⟨?_, ?_⟩
    · intro n
      simp [hx.1 n, hy.1 n]
    · intro n
      exact (twoCocycleSubgroup (action := actn n)).mul_mem (hx.2 n) (hy.2 n)
  inv_mem' hx := by
    refine ⟨?_, ?_⟩
    · intro n
      simp [hx.1 n]
    · intro n
      exact (twoCocycleSubgroup (action := actn n)).inv_mem (hx.2 n)

/-- The composite of the cochain exchange with the inclusion of the cochain
limit, as a homomorphism into the full product. -/
def twoCochainEquivPi :
    ContinuousTwoCochain (G := G) (A := LimCoeff A proj) →*
      (∀ n, ContinuousTwoCochain (G := G) (A := A n)) :=
  (twoCochainLim (G := G) A proj).subtype.comp (twoCochainEquiv G A proj).toMonoidHom

theorem twoCochainEquivPi_apply (c : ContinuousTwoCochain (G := G) (A := LimCoeff A proj))
    (n : ℕ) :
    twoCochainEquivPi A proj c n = twoCochainLevel A proj n c := rfl

theorem twoCochainEquivPi_injective :
    Function.Injective (twoCochainEquivPi (G := G) A proj) := by
  intro x y h
  apply (twoCochainEquiv G A proj).injective
  apply Subtype.ext
  exact h

/-- Characterisation of the image of the 2-cocycle subgroup under the cochain
exchange. -/
theorem mem_map_twoCocycle_iff {c : ∀ n, ContinuousTwoCochain (G := G) (A := A n)} :
    c ∈ Subgroup.map (twoCochainEquivPi A proj)
        (twoCocycleSubgroup (action := limitAction A proj actn compat)) ↔
      c ∈ twoCocycleLimFamily A proj actn := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · intro n
      apply ContinuousTwoCochain.ext
      intro x y'
      exact (y.1 (x, y')).2 n
    · intro n
      exact (mem_twoCocycle_iff_levels A proj actn compat y).mp hy n
  · rintro ⟨hcompat, hcocycle⟩
    refine ⟨(twoCochainEquiv G A proj).symm ⟨c, hcompat⟩, ?_, ?_⟩
    · refine (mem_twoCocycle_iff_levels A proj actn compat _).mpr ?_
      intro n
      have hcoord :
          twoCochainLevel A proj n ((twoCochainEquiv G A proj).symm ⟨c, hcompat⟩) = c n := by
        have h := congrArg
          (fun f : twoCochainLim (G := G) A proj =>
            (f : ∀ n, ContinuousTwoCochain (G := G) (A := A n)) n)
          (MulEquiv.apply_symm_apply (twoCochainEquiv G A proj) ⟨c, hcompat⟩)
        exact h
      rw [hcoord]
      exact hcocycle n
    · have h := MulEquiv.apply_symm_apply (twoCochainEquiv G A proj) ⟨c, hcompat⟩
      exact congrArg
        (fun f : twoCochainLim (G := G) A proj =>
          (f : ∀ n, ContinuousTwoCochain (G := G) (A := A n))) h

/-- **The Z2 exchange**: continuous 2-cocycles with values in the inverse limit
are the inverse limit of the level groups of continuous 2-cocycles. -/
noncomputable def twoCocycleExchange :
    ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
        (action := limitAction A proj actn compat) ≃*
      twoCocycleLimFamily A proj actn :=
  (Subgroup.equivMapOfInjective
      (twoCocycleSubgroup (action := limitAction A proj actn compat))
      (twoCochainEquivPi A proj) (twoCochainEquivPi_injective A proj)).trans
    (MulEquiv.subgroupCongr (Subgroup.ext fun c =>
      mem_map_twoCocycle_iff A proj actn compat))

theorem nonempty_twoCocycleExchange :
    Nonempty (ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
        (action := limitAction A proj actn compat) ≃*
      twoCocycleLimFamily A proj actn) :=
  ⟨twoCocycleExchange A proj actn compat⟩

end Cochains

/-! ## 5. The degree-two comparison with the level cohomologies -/

section H2Comparison

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : ℕ → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)
variable (actn : ∀ n, Iut.ContinuousGroupAction G (A n))
variable (compat : ∀ n (g : G) (x : A (n+1)),
  proj n ((actn (n+1)).act g x) = (actn n).act g (proj n x))

/-- The level-n projection of continuous 2-cocycles. -/
def twoCocycleLevel (n : ℕ) :
    ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
        (action := limitAction A proj actn compat) →*
      ContinuousTwoCocycle (G := G) (A := A n) (action := actn n) :=
  ((twoCochainLevel A proj n).comp
      (twoCocycleSubgroup (action := limitAction A proj actn compat)).subtype).codRestrict
    (twoCocycleSubgroup (action := actn n))
    (fun c => (mem_twoCocycle_iff_levels A proj actn compat c.1).mp c.2 n)

@[simp] theorem twoCocycleLevel_apply (n : ℕ)
    (c : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
      (action := limitAction A proj actn compat)) :
    (↑(twoCocycleLevel A proj actn compat n c) : ContinuousTwoCochain (G := G) (A := A n)) =
      twoCochainLevel A proj n (↑c) := rfl

/-- The transition map of continuous 2-cocycles. -/
def twoCocycleProj (n : ℕ) :
    ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1)) →*
      ContinuousTwoCocycle (G := G) (A := A n) (action := actn n) :=
  ((twoCochainProj A proj n).comp
      (twoCocycleSubgroup (action := actn (n+1))).subtype).codRestrict
    (twoCocycleSubgroup (action := actn n))
    (fun c => twoCochainProj_mem_twoCocycle A proj actn compat c.2)

@[simp] theorem twoCocycleProj_apply (n : ℕ)
    (c : ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1))) :
    (↑(twoCocycleProj A proj actn compat n c) : ContinuousTwoCochain (G := G) (A := A n)) =
      twoCochainProj A proj n (↑c) := rfl

/-- The transition maps commute with the level projections of 2-cocycles. -/
theorem twoCocycleProj_twoCocycleLevel (n : ℕ)
    (c : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
      (action := limitAction A proj actn compat)) :
    twoCocycleProj A proj actn compat n (twoCocycleLevel A proj actn compat (n+1) c) =
      twoCocycleLevel A proj actn compat n c := by
  apply Subtype.ext
  rw [twoCocycleProj_apply, twoCocycleLevel_apply]
  apply ContinuousTwoCochain.ext
  intro x y
  let hxy : LimCoeff A proj := (↑c : G × G → LimCoeff A proj) (x, y)
  change proj n ((hxy : ∀ m, A m) (n+1)) = (hxy : ∀ m, A m) n
  exact hxy.2 n

/- The first differential commutes with the projection of 1-cochains. -/
include compat in
theorem deltaOne_twoCochainProj (n : ℕ)
    (a : ContinuousOneCochain (G := G) (A := A (n+1))) :
    twoCochainProj A proj n (deltaOne (actn (n+1)) a) =
      deltaOne (actn n) (oneCochainProj A proj n a) := by
  apply ContinuousTwoCochain.ext
  intro g h
  simp [deltaOne, oneCochainProj_apply, twoCochainProj_coe_apply, map_mul, map_inv,
    compat n g (a.1 h)]

/-- Coboundaries project to coboundaries. -/
theorem deltaOneCocycle_twoCocycleProj (n : ℕ)
    (a : ContinuousOneCochain (G := G) (A := A (n+1))) :
    twoCocycleProj A proj actn compat n (deltaOneCocycle (actn (n+1)) a) =
      deltaOneCocycle (actn n) (oneCochainProj A proj n a) := by
  apply Subtype.ext
  exact deltaOne_twoCochainProj A proj actn compat n a

/-- The coboundary subgroup of the level n+1 maps into the coboundary subgroup
of the level n. -/
theorem coboundary_le_comap (n : ℕ) :
    coboundarySubgroup (action := actn (n+1)) ≤
      Subgroup.comap (twoCocycleProj A proj actn compat n)
        (coboundarySubgroup (action := actn n)) := by
  rintro c ⟨a, rfl⟩
  exact ⟨oneCochainProj A proj n a,
    (deltaOneCocycle_twoCocycleProj A proj actn compat n a).symm⟩

/-- The level-n projection of continuous H2. -/
def h2Proj (n : ℕ) :
    ContinuousH2 (G := G) (A := A (n+1)) (action := actn (n+1)) →*
      ContinuousH2 (G := G) (A := A n) (action := actn n) :=
  QuotientGroup.map (coboundarySubgroup (action := actn (n+1)))
    (coboundarySubgroup (action := actn n))
    (twoCocycleProj A proj actn compat n) (coboundary_le_comap A proj actn compat n)

@[simp] theorem h2Proj_mk (n : ℕ)
    (c : ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1))) :
    h2Proj A proj actn compat n (QuotientGroup.mk c) =
      QuotientGroup.mk (twoCocycleProj A proj actn compat n c) :=
  QuotientGroup.map_mk _ _ _ _ c

/-- The inverse limit of the continuous H2 groups, inside the product. -/
def LimH2 : Subgroup (∀ n, ContinuousH2 (G := G) (A := A n) (action := actn n)) :=
  limSubgroup (fun n => ContinuousH2 (G := G) (A := A n) (action := actn n))
    (fun n => h2Proj A proj actn compat n)

/-- The level classes of a continuous 2-cocycle of the limit, as an element of
the inverse limit of the level H2 groups. -/
def z2ToLimH2 :
    ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
        (action := limitAction A proj actn compat) →* LimH2 A proj actn compat where
  toFun c :=
    ⟨fun n => QuotientGroup.mk (twoCocycleLevel A proj actn compat n c), by
      intro n
      rw [h2Proj_mk, twoCocycleProj_twoCocycleLevel]⟩
  map_one' := by
    apply Subtype.ext
    funext n
    simp
  map_mul' c d := by
    apply Subtype.ext
    funext n
    simp

@[simp] theorem z2ToLimH2_apply
    (c : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
      (action := limitAction A proj actn compat)) (n : ℕ) :
    (z2ToLimH2 A proj actn compat c : ∀ n, ContinuousH2 (G := G) (A := A n) (action := actn n)) n =
      QuotientGroup.mk (twoCocycleLevel A proj actn compat n c) := rfl

/-- The level projection of a coboundary of the limit is the coboundary of the
projected 1-cochain. -/
theorem twoCocycleLevel_deltaOneCocycle (n : ℕ)
    (a : ContinuousOneCochain (G := G) (A := LimCoeff A proj)) :
    twoCocycleLevel A proj actn compat n
        (deltaOneCocycle (limitAction A proj actn compat) a) =
      deltaOneCocycle (actn n) (oneCochainLevel A proj n a) := by
  apply Subtype.ext
  apply ContinuousTwoCochain.ext
  intro g h
  simp [deltaOneCocycle, deltaOne, oneCochainLevel_apply, twoCochainLevel_apply,
    limitAction_act_apply]

/-- The class of a coboundary of the limit vanishes levelwise. -/
theorem z2ToLimH2_coboundary
    (c : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
      (action := limitAction A proj actn compat))
    (hc : c ∈ coboundarySubgroup (action := limitAction A proj actn compat)) :
    z2ToLimH2 A proj actn compat c = 1 := by
  obtain ⟨a, rfl⟩ := hc
  apply Subtype.ext
  funext n
  rw [Subgroup.coe_one, Pi.one_apply, z2ToLimH2_apply, QuotientGroup.eq_one_iff]
  exact ⟨oneCochainLevel A proj n a,
    (twoCocycleLevel_deltaOneCocycle A proj actn compat n a).symm⟩

/-- **The comparison map** from the continuous H2 of the limit to the inverse
limit of the level continuous H2 groups. -/
noncomputable def h2Comparison :
    ContinuousH2 (G := G) (A := LimCoeff A proj) (action := limitAction A proj actn compat) →*
      LimH2 A proj actn compat :=
  QuotientGroup.lift (coboundarySubgroup (action := limitAction A proj actn compat))
    (z2ToLimH2 A proj actn compat)
    (by
      intro c hc
      rw [MonoidHom.mem_ker]
      exact z2ToLimH2_coboundary A proj actn compat c hc)

@[simp] theorem h2Comparison_mk
    (c : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
      (action := limitAction A proj actn compat)) :
    h2Comparison A proj actn compat (QuotientGroup.mk c) =
      z2ToLimH2 A proj actn compat c :=
  QuotientGroup.lift_mk _ _ c

/-- **The coboundary lift**: a continuous 2-cocycle of the limit whose every
level projection is a level coboundary is itself a coboundary.  This is the
lim^1 vanishing input for the degree-two exchange; it is not a topological
API gap. -/
def CoboundaryLift : Prop :=
  ∀ (c : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
      (action := limitAction A proj actn compat)),
    (∀ n, twoCocycleLevel A proj actn compat n c ∈
      coboundarySubgroup (action := actn n)) →
      c ∈ coboundarySubgroup (action := limitAction A proj actn compat)

/-- **The comparison map is injective exactly when the coboundary lift holds.** -/
theorem h2Comparison_injective_iff :
    Function.Injective (h2Comparison A proj actn compat) ↔
      CoboundaryLift A proj actn compat := by
  constructor
  · intro hinj c hlev
    have h1 : z2ToLimH2 A proj actn compat c = 1 := by
      apply Subtype.ext
      funext n
      rw [Subgroup.coe_one, Pi.one_apply, z2ToLimH2_apply, QuotientGroup.eq_one_iff]
      exact hlev n
    have hmk : QuotientGroup.mk (s := coboundarySubgroup (action := limitAction A proj actn compat)) c = 1 := by
      apply hinj
      rw [h2Comparison_mk, h1, map_one]
    exact (QuotientGroup.eq_one_iff c).mp hmk
  · intro hl x y hxy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
      (coboundarySubgroup (action := limitAction A proj actn compat)) x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective
      (coboundarySubgroup (action := limitAction A proj actn compat)) y
    have hz : z2ToLimH2 A proj actn compat c = z2ToLimH2 A proj actn compat d := by
      rw [← h2Comparison_mk, ← h2Comparison_mk]
      exact hxy
    have hcn : ∀ n, QuotientGroup.mk (s := coboundarySubgroup (action := actn n))
          (twoCocycleLevel A proj actn compat n c) =
        QuotientGroup.mk (s := coboundarySubgroup (action := actn n))
          (twoCocycleLevel A proj actn compat n d) := by
      intro n
      have h := congrArg
        (fun z : LimH2 A proj actn compat =>
          (z : ∀ n, ContinuousH2 (G := G) (A := A n) (action := actn n)) n) hz
      rwa [z2ToLimH2_apply, z2ToLimH2_apply] at h
    have hcd : (c / d) ∈ coboundarySubgroup (action := limitAction A proj actn compat) := by
      refine hl (c / d) ?_
      intro n
      have hmem : (twoCocycleLevel A proj actn compat n c)⁻¹ *
          (twoCocycleLevel A proj actn compat n d) ∈
            coboundarySubgroup (action := actn n) :=
        QuotientGroup.eq.mp (hcn n)
      have hinv := (coboundarySubgroup (action := actn n)).inv_mem hmem
      have hdiv : twoCocycleLevel A proj actn compat n c /
          twoCocycleLevel A proj actn compat n d ∈ coboundarySubgroup (action := actn n) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hinv
      have hmap : twoCocycleLevel A proj actn compat n (c / d) =
          twoCocycleLevel A proj actn compat n c /
            twoCocycleLevel A proj actn compat n d :=
        map_div _ c d
      rw [hmap]
      exact hdiv
    refine QuotientGroup.eq.mpr ?_
    have hinv : (c / d)⁻¹ ∈ coboundarySubgroup (action := limitAction A proj actn compat) :=
      Subgroup.inv_mem _ hcd
    have hEq : (c⁻¹ * d : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
        (action := limitAction A proj actn compat)) = (c / d)⁻¹ := by
      apply Subtype.ext
      apply ContinuousTwoCochain.ext
      intro x y
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    rw [hEq]
    exact hinv
/-! ## 6. The logical relation to the degree-two exchange -/

/-- The degree-two exchange (bijectivity of the comparison) implies the
coboundary lift. -/
theorem coboundaryLift_of_bijective
    (h : Function.Bijective (h2Comparison A proj actn compat)) :
    CoboundaryLift A proj actn compat :=
  (h2Comparison_injective_iff A proj actn compat).mp h.1

/-- The coboundary lift together with surjectivity of the comparison is the
degree-two exchange. -/
theorem bijective_of_coboundaryLift_of_surjective
    (hl : CoboundaryLift A proj actn compat)
    (hsurj : Function.Surjective (h2Comparison A proj actn compat)) :
    Function.Bijective (h2Comparison A proj actn compat) :=
  ⟨(h2Comparison_injective_iff A proj actn compat).mpr hl, hsurj⟩

end H2Comparison

/-! ## 7. Axiom probes -/

#print axioms continuous_isLocallyConstant_of_discrete
#print axioms compact_totallyDisconnected_isLocallyConstant
#print axioms finite_range_of_compact_of_discrete
#print axioms continuous_lim_iff
#print axioms oneCochainEquiv
#print axioms twoCochainEquiv
#print axioms deltaTwo_coord
#print axioms mem_twoCocycle_iff_levels
#print axioms twoCocycleExchange
#print axioms nonempty_twoCocycleExchange
#print axioms twoCocycleProj_twoCocycleLevel
#print axioms deltaOne_twoCochainProj
#print axioms twoCocycleLevel_deltaOneCocycle
#print axioms h2Comparison
#print axioms CoboundaryLift
#print axioms h2Comparison_injective_iff
#print axioms coboundaryLift_of_bijective
#print axioms bijective_of_coboundaryLift_of_surjective

end LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual