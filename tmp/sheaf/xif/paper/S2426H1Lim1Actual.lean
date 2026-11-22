import tmp.sheaf.xif.paper.S2114H2SurjectivityGapActual
import tmp.sheaf.xif.paper.S2138H1MLActual
import tmp.sheaf.xif.paper.S2142ActualH1TowerActual
import tmp.sheaf.xif.paper.S2145MuH1InstanceActual
import tmp.sheaf.xif.paper.S2196ActionContinuousProofActual
import tmp.sheaf.xif.paper.S2204ActualH1InstanceActual
import tmp.sheaf.xif.paper.S2214H1MonoidActual
import tmp.sheaf.xif.paper.S2410H1EquivDoneActual
import tmp.sheaf.xif.paper.S2420H1InstanceFiniteActual

/-!
# S2426: the first derived limit lim¹ H¹ of the actual H¹ tower

Layer: **O**.  Consumers: S2114 (S2114CompatibleRepresentativeLift,
S2114H2ComparisonSurjective) and, through it, the degree-two limit exchange
of S2112.

## What is proved here

1. **The actual tower.**  The arithmetic H¹ tower of S2204/S2214,
   n ↦ H¹(G_v, μ_{n!}), with the power transition S2214H1PushforwardHom,
   is a genuine S2138H1Tower (S2426ActualH1Tower): every level is finite by
   the *unconditional* Kummer comparison of S2410, and the transition is the
   verified quotient monoid homomorphism of S2214.  No surjectivity input is
   needed for this tower.  Building the S2145/S2142 instance additionally
   requires transition surjectivity, isolated in the real structure
   S2426ActualH1TransitionSurjective; that structure has no inhabitant here.

2. **Mittag-Leffler, unconditionally.**  Every tower of finite groups is
   Mittag-Leffler: the ranges of the iterated transitions form a decreasing
   sequence inside the finite group H¹_n, so their cardinalities (a decreasing
   sequence of natural numbers) stabilize.  This gives
   S2426MittagLeffler_of_finite, and for the actual tower
   S2426ActualMittagLeffler with no hypotheses at all.  The easier route
   through S2138 (S2426ActualMittagLeffler_of_surjective) is also recorded.

3. **lim¹ (the API that was missing).**  The first derived limit of a tower of
   abelian groups is defined here: S2426Lim1 T is the quotient of ∏ n, H¹_n by
   the subgroup of coboundaries y n * (φ n (y (n+1)))⁻¹.
   S2426Lim1_subsingleton_of_surjective proves that surjective transitions
   make it trivial.  For the actual tower this yields
   S2426ActualH1Lim1_subsingleton, i.e. lim¹ H¹ = 0, under the explicit
   arithmetic input S2426ActualH1TransitionSurjective.

4. **The S2114 link.**  The actual arithmetic instance
   S2426ActualCompatibleRepresentativeLift of
   S2114CompatibleRepresentativeLift is stated for the actual coefficient
   tower μ_{n!}, together with the two implications of S2114 (a lift gives
   surjectivity of the actual degree-two comparison; conversely surjectivity
   produces a lift).  No inhabitant is produced.

## Not claimed

* **No unconditional surjectivity of h2Comparison.**  The equivalence of
  S2426ActualH2Comparison being surjective with the nonemptiness of the lift
  structure is recorded in both directions; neither side is proved here.
* The countable Mittag-Leffler lemma (lim¹ = 0 for every ML system) is not
  formalized.  Vanishing is obtained from transition surjectivity, not from
  the (unconditional) Mittag-Leffler condition alone.

## Not run

Full lake build, comparator, and independent source-semantics review; only
this file is elaborated below.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2426H1Lim1Actual

open Iut
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual
open LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual
open LeanFormal.IUT.XiFPaper.S2138H1MLActual
open LeanFormal.IUT.XiFPaper.S2142ActualH1TowerActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
open LeanFormal.IUT.XiFPaper.S2420H1InstanceFiniteActual

/-! ## 1. The actual H¹ tower -/

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The exact arithmetic input still missing: the power transition
H¹(G_v, μ_{(n+1)!}) → H¹(G_v, μ_{n!}) of the actual tower is surjective.
A real structure with a real mathematical field (not True); no inhabitant is
asserted. -/
structure S2426ActualH1TransitionSurjective : Prop where
  proj_surjective : ∀ n, Function.Surjective (⇑(S2214H1PushforwardHom p n))

theorem S2426ActualH1TransitionSurjective_iff :
    S2426ActualH1TransitionSurjective p ↔
      ∀ n, Function.Surjective (⇑(S2214H1PushforwardHom p n)) :=
  ⟨fun h => h.proj_surjective, fun h => ⟨h⟩⟩

/-- Unconditional finiteness of every actual level H¹(G_v, μ_{n!}), from the
Kummer comparison of S2410. -/
theorem S2426ActualH1Finite (n : ℕ) : Finite (S2204H1 p n) :=
  S2410FiniteH1 p n

/-- The actual H¹ tower as an abstract S2138H1Tower, with the verified power
transitions and the unconditional finite levels.  No surjectivity input is
needed here. -/
noncomputable def S2426ActualH1Tower : S2138H1Tower where
  H1 := S2204H1 p
  finite := fun n => S2410FiniteH1 p n
  proj := fun n => S2214H1PushforwardHom p n

theorem S2426ActualH1Tower_proj (n : ℕ) :
    (S2426ActualH1Tower p).proj n = S2214H1PushforwardHom p n := rfl

/-- With transition surjectivity, the actual tower is an
S2138ActualMuH1Tower (the exact structure consumed by S2138). -/
noncomputable def S2426ActualMuH1Tower
    (h : S2426ActualH1TransitionSurjective p) : S2138ActualMuH1Tower where
  H1 := S2204H1 p
  finite := fun n => S2410FiniteH1 p n
  proj := fun n => S2214H1PushforwardHom p n
  proj_surjective := h.proj_surjective

/-- The S2214 remaining data, with finiteness now actual and only
surjectivity assumed (through S2420). -/
noncomputable def S2426ActualS2145Instance
    (h : S2426ActualH1TransitionSurjective p) : S2145ActualMuH1Instance p :=
  S2420ToS2145Instance p h.proj_surjective

/-- The actual S2142 tower (the structure S2142 proves the Mittag-Leffler
statement for). -/
noncomputable def S2426ActualS2142Tower
    (h : S2426ActualH1TransitionSurjective p) : S2142ActualMuH1Tower :=
  S2145ToS2142 p (S2426ActualS2145Instance p h)

/-- Mittag-Leffler for the actual tower, through the S2142 instance. -/
theorem S2426ActualMittagLeffler_of_s2142
    (h : S2426ActualH1TransitionSurjective p) :
    S2138MittagLeffler (S2142ToS2138Tower (S2426ActualS2142Tower p h)) :=
  S2142MittagLeffler (S2426ActualS2142Tower p h)

/-- Mittag-Leffler for the actual tower, directly through S2138 and the same
surjectivity input. -/
theorem S2426ActualMittagLeffler_of_surjective
    (h : S2426ActualH1TransitionSurjective p) :
    S2138MittagLeffler (S2426ActualH1Tower p) :=
  S2138MittagLeffler_of_surjective (S2426ActualH1Tower p) h.proj_surjective

/-! ## 2. Mittag-Leffler from finiteness alone

For finite levels the ranges of the iterated transitions are a decreasing
sequence of subsets of a finite group, so their cardinalities stabilize.  This
removes the surjectivity hypothesis from the Mittag-Leffler condition. -/

/-- The ranges of the iterated transition maps are antitone. -/
theorem S2426IterProj_range_antitone (T : S2138H1Tower) (n : ℕ) :
    Antitone fun r => Set.range (S2138IterProj T n r) := by
  intro r s hrs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      refine subset_trans ?_ (ih (Nat.le_add_right r k))
      rintro z ⟨x, rfl⟩
      exact ⟨T.proj (n + (r + k)) x, rfl⟩

/-- An antitone sequence of natural numbers is eventually constant: the
minimum of its range is attained. -/
theorem S2426Nat_antitone_eventually_const (f : ℕ → ℕ) (hf : Antitone f) :
    ∃ r, ∀ m, r ≤ m → f m = f r := by
  have hne : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  obtain ⟨r, hr⟩ := Nat.sInf_mem hne
  refine ⟨r, fun m hm => ?_⟩
  refine le_antisymm (hf hm) ?_
  rw [hr]
  exact Nat.sInf_le ⟨m, rfl⟩

/-- **Every tower of finite groups is Mittag-Leffler.** -/
theorem S2426MittagLeffler_of_finite (T : S2138H1Tower) :
    S2138MittagLeffler T := by
  intro n
  let f : ℕ → ℕ := fun r => (Set.range (S2138IterProj T n r)).ncard
  have hf : Antitone f := by
    intro r s hrs
    exact Set.ncard_le_ncard (S2426IterProj_range_antitone T n hrs) (Set.toFinite _)
  obtain ⟨r, hr⟩ := S2426Nat_antitone_eventually_const f hf
  refine ⟨r, fun s => ?_⟩
  have hsub : Set.range (S2138IterProj T n (r+s)) ⊆
      Set.range (S2138IterProj T n r) :=
    S2426IterProj_range_antitone T n (Nat.le_add_right r s)
  have hcard : (Set.range (S2138IterProj T n r)).ncard ≤
      (Set.range (S2138IterProj T n (r+s))).ncard :=
    le_of_eq (hr (r + s) (Nat.le_add_right r s)).symm
  exact Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)

/-- **Mittag-Leffler for the actual H¹ tower, unconditionally.** -/
theorem S2426ActualMittagLeffler :
    S2138MittagLeffler (S2426ActualH1Tower p) :=
  S2426MittagLeffler_of_finite (S2426ActualH1Tower p)

/-! ## 3. The first derived limit lim¹ of an abelian tower -/

section Lim1

variable (T : S2138H1Tower)

/-- The lim¹ coboundary homomorphism of the tower:
y ↦ (y n * (φ n (y (n+1)))⁻¹). -/
noncomputable def S2426Delta : (∀ n, T.H1 n) →* (∀ n, T.H1 n) where
  toFun x := fun n => x n * (T.proj n (x (n+1)))⁻¹
  map_one' := by
    funext n
    simp
  map_mul' x y := by
    funext n
    show (x n * y n) * (T.proj n (x (n+1) * y (n+1)))⁻¹ =
      (x n * (T.proj n (x (n+1)))⁻¹) *
        (y n * (T.proj n (y (n+1)))⁻¹)
    rw [map_mul, mul_inv_rev]
    simp [mul_comm, mul_left_comm, mul_assoc]

@[simp] theorem S2426Delta_apply (x : ∀ n, T.H1 n) (n : ℕ) :
    S2426Delta T x n = x n * (T.proj n (x (n+1)))⁻¹ := rfl

/-- The subgroup of lim¹ coboundaries. -/
noncomputable def S2426Coboundary : Subgroup (∀ n, T.H1 n) :=
  (S2426Delta T).range

/-- The first derived limit lim¹_n H¹_n, as an abelian group. -/
noncomputable abbrev S2426Lim1 : Type :=
  (∀ n, T.H1 n) ⧸ S2426Coboundary T

instance S2426Lim1Pi_isMulCommutative : IsMulCommutative (∀ n, T.H1 n) :=
  IsMulCommutative.of_comm fun a b => mul_comm a b

instance S2426Coboundary_normal : (S2426Coboundary T).Normal :=
  Subgroup.normal_of_isMulCommutative (S2426Coboundary T)

/-- A simultaneous solution of the lim¹ equation
y n = x n * (φ n (y (n+1))), built backwards from y 0 = 1 using
surjectivity of the transitions. -/
noncomputable def S2426Lim1Lift
    (h : ∀ n, Function.Surjective (T.proj n)) (x : ∀ n, T.H1 n) :
    ∀ n, T.H1 n :=
  Nat.rec (motive := fun n => T.H1 n) 1
    (fun n y => Classical.choose (h n ((x n)⁻¹ * y)))

/-- The lift solves the lim¹ equation at every level. -/
theorem S2426Lim1Lift_spec
    (h : ∀ n, Function.Surjective (T.proj n)) (x : ∀ n, T.H1 n) :
    ∀ n, S2426Lim1Lift T h x n * (T.proj n (S2426Lim1Lift T h x (n+1)))⁻¹ = x n
  | 0 => by
      have h1 : T.proj 0 (S2426Lim1Lift T h x 1) =
          (x 0)⁻¹ * S2426Lim1Lift T h x 0 :=
        Classical.choose_spec (h 0 ((x 0)⁻¹ * S2426Lim1Lift T h x 0))
      have h0 : S2426Lim1Lift T h x 0 = 1 := rfl
      rw [h1, h0]
      simp
  | n+1 => by
      have h1 : T.proj (n+1) (S2426Lim1Lift T h x (n+1+1)) =
          (x (n+1))⁻¹ * S2426Lim1Lift T h x (n+1) :=
        Classical.choose_spec (h (n+1) ((x (n+1))⁻¹ * S2426Lim1Lift T h x (n+1)))
      rw [h1, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Every element of ∏ n, H¹_n is a lim¹ coboundary when transitions are
surjective. -/
theorem S2426Lim1_mk_eq_one
    (h : ∀ n, Function.Surjective (T.proj n)) (x : ∀ n, T.H1 n) :
    (x : (∀ n, T.H1 n) ⧸ S2426Coboundary T) = 1 :=
  (QuotientGroup.eq_one_iff (N := S2426Coboundary T) x).mpr
    ⟨S2426Lim1Lift T h x, funext (S2426Lim1Lift_spec T h x)⟩

/-- The first derived limit is the trivial group when transitions are
surjective. -/
theorem S2426Lim1_eq_one
    (h : ∀ n, Function.Surjective (T.proj n)) (z : S2426Lim1 T) : z = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (S2426Coboundary T) z
  exact S2426Lim1_mk_eq_one T h x

/-- **lim¹_n H¹_n = 0 under surjective transitions.** -/
theorem S2426Lim1_subsingleton_of_surjective
    (h : ∀ n, Function.Surjective (T.proj n)) : Subsingleton (S2426Lim1 T) :=
  ⟨fun a b => by rw [S2426Lim1_eq_one T h a, S2426Lim1_eq_one T h b]⟩

end Lim1

/-! ## 4. lim¹ H¹ = 0 for the actual tower -/

/-- The first derived limit of the actual H¹ tower. -/
noncomputable abbrev S2426ActualH1Lim1 : Type :=
  S2426Lim1 (S2426ActualH1Tower p)

/-- **lim¹ H¹ = 0 for the actual tower**, from the explicit arithmetic
transition-surjectivity input. -/
theorem S2426ActualH1Lim1_subsingleton
    (h : S2426ActualH1TransitionSurjective p) :
    Subsingleton (S2426ActualH1Lim1 p) :=
  S2426Lim1_subsingleton_of_surjective (S2426ActualH1Tower p) h.proj_surjective

theorem S2426ActualH1Lim1_eq_one
    (h : S2426ActualH1TransitionSurjective p) (z : S2426ActualH1Lim1 p) :
    z = 1 :=
  S2426Lim1_eq_one (S2426ActualH1Tower p) h.proj_surjective z

/-! ## 5. The S2114 representative lift for the actual coefficient tower

The coefficient tower is μ_{n!} with the power transition S2145PowMap and the
Galois action of S2196MuActionTower.  The S2114 structure is stated here for
that tower; it is *not* inhabited, and no surjectivity of h2Comparison is
claimed. -/

section ActualH2

/-- The actual inverse limit of the level groups H²(G_v, μ_{n!}). -/
noncomputable abbrev S2426ActualLimH2 :
    Subgroup ((n : ℕ) → ContinuousH2 (G := LocalAbsoluteGalois p)
      (A := S2145Coeff p n) (action := (S2196MuActionTower p).actn n)) :=
  LimH2 (S2145Coeff p) (S2145PowMap p) (S2196MuActionTower p).actn
    (S2196MuActionTower p).compat

/-- The actual degree-two comparison. -/
noncomputable def S2426ActualH2Comparison :
    ContinuousH2 (G := LocalAbsoluteGalois p)
      (A := LimCoeff (S2145Coeff p) (S2145PowMap p))
      (action := limitAction (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn (S2196MuActionTower p).compat) →*
      S2426ActualLimH2 p :=
  h2Comparison (S2145Coeff p) (S2145PowMap p) (S2196MuActionTower p).actn
    (S2196MuActionTower p).compat

/-- The S2114 representative lift for the actual coefficient tower.  Its
fields are real mathematical data: a choice of continuous 2-cocycle of the
inverse limit over each compatible family of level H² classes, with the
specified level projections.  No inhabitant is constructed here. -/
noncomputable abbrev S2426ActualCompatibleRepresentativeLift : Type :=
  S2114CompatibleRepresentativeLift (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat

/-- A lift gives surjectivity of the actual degree-two comparison
(conditional; nothing is asserted unconditionally). -/
theorem S2426ActualH2Comparison_surjective_of_lift
    (L : S2426ActualCompatibleRepresentativeLift p) :
    Function.Surjective (S2426ActualH2Comparison p) :=
  S2114_surjective_of_representativeLift (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat L

/-- Conversely, surjectivity of the actual comparison produces a lift
(S2114, converse direction). -/
theorem S2426ActualCompatibleRepresentativeLift_nonempty_of_surjective
    (h : Function.Surjective (S2426ActualH2Comparison p)) :
    Nonempty (S2426ActualCompatibleRepresentativeLift p) :=
  S2114_representativeLift_of_surjective (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat h

/-- The exact lim¹-type obstruction of S2112 for the actual tower:
injectivity of the actual degree-two comparison is equivalent to the
coboundary-lift condition for the actual coefficient system. -/
theorem S2426ActualH2Comparison_injective_iff :
    Function.Injective (S2426ActualH2Comparison p) ↔
      CoboundaryLift (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn (S2196MuActionTower p).compat :=
  h2Comparison_injective_iff (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat

end ActualH2

/-! ## 6. Axiom probes -/

#print axioms S2426ActualH1Tower
#print axioms S2426MittagLeffler_of_finite
#print axioms S2426ActualMittagLeffler
#print axioms S2426Lim1_subsingleton_of_surjective
#print axioms S2426ActualH1Lim1_subsingleton
#print axioms S2426ActualH2Comparison_surjective_of_lift
#print axioms S2426ActualH2Comparison_injective_iff

end LeanFormal.IUT.XiFPaper.S2426H1Lim1Actual
end
