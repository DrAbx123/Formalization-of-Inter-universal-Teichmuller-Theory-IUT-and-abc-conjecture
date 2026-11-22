import tmp.sheaf.xif.paper.S2114H2SurjectivityGapActual
import tmp.sheaf.xif.paper.S2138H1MLActual
import tmp.sheaf.xif.paper.S2196ActionContinuousProofActual

/-!
# S2427: the compatible representative for the inverse limit of H^2

Layer: **O**.  Consumer: S2114 (S2114CompatibleRepresentativeLift,
S2114H2ComparisonSurjective) and, through it, the degree-two exchange of S2112.

## What is proved here (unconditional; no sorry, no new axioms)

The degree-two comparison of S2112 is

  h2Comparison : H^2_cont(G, lim A) ->* lim_n H^2_cont(G, A_n).

S2114 isolated the exact cocycle-level datum producing surjectivity, a
*compatible representative*: for every compatible family of level H^2 classes a
single continuous 2-cocycle of the limit whose level classes are the given ones.

1. **Assembly (unconditional).**  A compatible family of level 2-cocycles
   (already compatible under the level projection) assembles into a continuous
   2-cocycle of the limit whose level projections are the given cocycles
   (limitCochain, twoCochainLevel_limitCochain).

2. **The correction recursion (the actual construction).**  The naive choice of
   level cocycle representatives is not compatible: the ratio of the projection
   of a level n+1 representative and a level n representative is a level n
   coboundary.  This file corrects the representatives inductively: if the
   coefficient transition proj n : A (n+1) ->* A n is surjective, then every
   continuous 1-cochain at level n is the projection of a continuous 1-cochain
   at level n+1 (oneCochainProj_surjective), and the correction is solveable at
   every level (correctNext, correctNext_proj, correctNext_class).  No
   finiteness, no lim^1 input and no choice of a splitting is used; only
   Classical.choose of the transition surjectivity.

3. **Surjectivity of the comparison (unconditional).**
   h2Comparison_surjective_of_coeff_surjective: if every coefficient transition
   is surjective then h2Comparison is surjective.  Hence a compatible
   representative lift in the sense of S2114 exists
   (representativeLift_of_coeff_surjective), and the two S2114 directions are
   recorded as an equivalence (nonempty_representativeLift_iff_surjective).

4. **The actual arithmetic tower.**  The actual coefficient tower is
   S2145Coeff p n = mu_{n!}, with the actual power transition S2145PowMap p n
   and the actual compatible continuous action (S2196MuActionTower p).actn of
   the local absolute Galois group Gal(Qbar_p / Q_p).  Its coefficient
   transitions are surjective (S2427PowMap_surjective): X^(n+1) = omega is
   solveable in the algebraic closure.  Consequently the **actual** H^2
   comparison of the mu_{n!} tower is surjective
   (S2427ActualH2Comparison_surjective) and the actual compatible
   representative lift exists (S2427ActualRepresentativeLift).

5. **The remaining input.**  Surjectivity needs no homological input.
   *Injectivity* of the comparison is, by S2112, exactly the coboundary lift
   (CoboundaryLift), i.e. the lim^1-vanishing of level H^1.  This file states
   that input as a named proposition on the level H^1 tower
   (OneCocycleProjSurjective, levelH1Tower) and shows how the S2138
   Mittag-Leffler condition follows from surjectivity of the level transitions;
   it does **not** assert an inhabitant.

## Not run

Full lake build of the project, comparator and independent source-semantics
review are not part of this file.  The axiom probes at the end use only the
three standard axioms.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u

namespace LeanFormal.IUT.XiFPaper.S2427H2CompatRepActual

open Iut
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual
open LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual

/-! ## 1. Coefficient-surjective transitions lift 1-cochains

If the coefficient transition proj n : A (n+1) ->* A n is surjective, then
every continuous 1-cochain at level n is the projection of one at level n+1:
choose a preimage of each value.  A function constant on the (open) fibres of a
locally constant map is locally constant. -/

section CochainLift

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Nat → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)

/-- Surjectivity of the coefficient transition lifts continuous 1-cochains. -/
theorem oneCochainProj_surjective (hproj : ∀ n, Function.Surjective (proj n)) (n : Nat) :
    Function.Surjective (oneCochainProj A proj n) := by
  intro c
  let s : A n → A (n+1) := fun v => Classical.choose (hproj n v)
  have hs : ∀ v, proj n (s v) = v := fun v => Classical.choose_spec (hproj n v)
  refine ⟨⟨fun x => s (c.1 x), ?_⟩, ?_⟩
  · have hc : IsLocallyConstant c.1 := continuous_isLocallyConstant_of_discrete c.2
    exact (IsLocallyConstant.iff_continuous (fun x => s (c.1 x))).mp (hc.comp s)
  · apply Subtype.ext
    funext x
    exact hs (c.1 x)

end CochainLift

/-! ## 2. Assembling a limit cochain out of a compatible family -/

section Assembly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Nat → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)

/-- The underlying function of the limit cochain of a compatible family of
level 2-cochains. -/
noncomputable def limitFun (cs : ∀ n, ContinuousTwoCochain (G := G) (A := A n))
    (hcompat : ∀ n, twoCochainProj A proj n (cs (n+1)) = cs n) :
    G × G → LimCoeff A proj :=
  fun p => ⟨fun n => (cs n).1 p, by
    intro n
    have h := congrArg (fun f : ContinuousTwoCochain (G := G) (A := A n) => f.1 p) (hcompat n)
    simpa [twoCochainProj_coe_apply] using h⟩

theorem limitFun_continuous (cs : ∀ n, ContinuousTwoCochain (G := G) (A := A n))
    (hcompat : ∀ n, twoCochainProj A proj n (cs (n+1)) = cs n) :
    Continuous (limitFun A proj cs hcompat) := by
  rw [continuous_lim_iff]
  intro n
  exact (cs n).2

/-- A compatible family of level 2-cochains assembles into a continuous
2-cochain of the limit. -/
noncomputable def limitCochain (cs : ∀ n, ContinuousTwoCochain (G := G) (A := A n))
    (hcompat : ∀ n, twoCochainProj A proj n (cs (n+1)) = cs n) :
    ContinuousTwoCochain (G := G) (A := LimCoeff A proj) :=
  ⟨limitFun A proj cs hcompat, limitFun_continuous A proj cs hcompat⟩

/-- The level projections of the assembled cochain are the given ones. -/
theorem twoCochainLevel_limitCochain (cs : ∀ n, ContinuousTwoCochain (G := G) (A := A n))
    (hcompat : ∀ n, twoCochainProj A proj n (cs (n+1)) = cs n) (n : Nat) :
    twoCochainLevel A proj n (limitCochain A proj cs hcompat) = cs n := by
  apply ContinuousTwoCochain.ext
  intro x y
  rfl

/-- The level projections of a limit 2-cochain are compatible. -/
theorem twoCochainProj_twoCochainLevel
    (c : ContinuousTwoCochain (G := G) (A := LimCoeff A proj)) (n : Nat) :
    twoCochainProj A proj n (twoCochainLevel A proj (n+1) c) =
      twoCochainLevel A proj n c := by
  apply ContinuousTwoCochain.ext
  intro x y
  rw [twoCochainProj_coe_apply, twoCochainLevel_apply, twoCochainLevel_apply]
  exact (↑c (x, y)).2 n

end Assembly

/-! ## 3. The correction recursion

Given a compatible family y of level H^2 classes, choose arbitrary level cocycle
representatives.  The projection of a level n+1 representative and the chosen
level n representative differ by a coboundary delta a.  Multiplying the level
n+1 representative by the coboundary of a *lift* of a 1-cochain whose
coboundary is (delta a)^-1 makes the projections agree, without changing the
level class. -/

section Representative

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Nat → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)
variable (actn : ∀ n, Iut.ContinuousGroupAction G (A n))
variable (compat : ∀ n (g : G) (x : A (n+1)),
  proj n ((actn (n+1)).act g x) = (actn n).act g (proj n x))

/-- A chosen level-n 2-cocycle representative of the level class y n. -/
noncomputable def levelRep (y : LimH2 A proj actn compat) (n : Nat) :
    ContinuousTwoCocycle (G := G) (A := A n) (action := actn n) :=
  Classical.choose (QuotientGroup.mk'_surjective
    (coboundarySubgroup (action := actn n))
    ((y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n))

theorem levelRep_mk (y : LimH2 A proj actn compat) (n : Nat) :
    QuotientGroup.mk (levelRep A proj actn compat y n) =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n :=
  Classical.choose_spec (QuotientGroup.mk'_surjective
    (coboundarySubgroup (action := actn n))
    ((y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n))

/-- Multiplying a 2-cocycle by the coboundary of a 1-cochain does not change
its class. -/
theorem mk_mul_deltaOneCocycle (n : Nat)
    (w : ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1)))
    (c : ContinuousOneCochain (G := G) (A := A (n+1))) :
    QuotientGroup.mk (w * deltaOneCocycle (actn (n+1)) c) = QuotientGroup.mk w := by
  refine QuotientGroup.eq_iff_div_mem.mpr ?_
  have hdiv : (w * deltaOneCocycle (actn (n+1)) c) / w = deltaOneCocycle (actn (n+1)) c := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hdiv]
  exact MonoidHom.mem_range.mpr ⟨c, rfl⟩

/-- The defect of two level representatives of the same class: the ratio of the
projection of the level n+1 representative and the level n representative is
the coboundary of a continuous 1-cochain. -/
theorem exists_defect (y : LimH2 A proj actn compat) (n : Nat)
    (z : ContinuousTwoCocycle (G := G) (A := A n) (action := actn n))
    (hz : QuotientGroup.mk z =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n)
    (w : ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1)))
    (hw : QuotientGroup.mk w =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) (n+1)) :
    ∃ a : ContinuousOneCochain (G := G) (A := A n),
      twoCocycleProj A proj actn compat n w = z * deltaOneCocycle (actn n) a := by
  have hcls : QuotientGroup.mk (twoCocycleProj A proj actn compat n w) = QuotientGroup.mk z := by
    rw [← h2Proj_mk, hw, hz]
    exact (y : LimH2 A proj actn compat).2 n
  have hmem : twoCocycleProj A proj actn compat n w / z ∈
      coboundarySubgroup (action := actn n) :=
    QuotientGroup.eq_iff_div_mem.mp hcls
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨a, ?_⟩
  rw [ha]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- A 1-cochain whose coboundary is the inverse of a prescribed coboundary. -/
theorem exists_neg_delta (n : Nat) (a : ContinuousOneCochain (G := G) (A := A n)) :
    ∃ c : ContinuousOneCochain (G := G) (A := A n),
      deltaOneCocycle (actn n) c = (deltaOneCocycle (actn n) a)⁻¹ := by
  have hmem : (deltaOneCocycle (actn n) a)⁻¹ ∈ coboundarySubgroup (action := actn n) :=
    Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨c, hc⟩

/-- The chosen correction 1-cochain at level n. -/
noncomputable def corrCochain (n : Nat) (a : ContinuousOneCochain (G := G) (A := A n)) :
    ContinuousOneCochain (G := G) (A := A n) :=
  Classical.choose (exists_neg_delta A proj actn compat n a)

theorem corrCochain_spec (n : Nat) (a : ContinuousOneCochain (G := G) (A := A n)) :
    deltaOneCocycle (actn n) (corrCochain A proj actn compat n a) =
      (deltaOneCocycle (actn n) a)⁻¹ :=
  Classical.choose_spec (exists_neg_delta A proj actn compat n a)

/-- A chosen lift of a continuous 1-cochain along a surjective coefficient
transition. -/
noncomputable def liftCochain (hproj : ∀ n, Function.Surjective (proj n)) (n : Nat)
    (c : ContinuousOneCochain (G := G) (A := A n)) :
    ContinuousOneCochain (G := G) (A := A (n+1)) :=
  Classical.choose (oneCochainProj_surjective A proj hproj n c)

theorem liftCochain_spec (hproj : ∀ n, Function.Surjective (proj n)) (n : Nat)
    (c : ContinuousOneCochain (G := G) (A := A n)) :
    oneCochainProj A proj n (liftCochain A proj hproj n c) = c :=
  Classical.choose_spec (oneCochainProj_surjective A proj hproj n c)

/-- The corrected level n+1 representative: the level class is unchanged and the
projection is the corrected level n representative. -/
noncomputable def correctNext (hproj : ∀ n, Function.Surjective (proj n))
    (y : LimH2 A proj actn compat) (n : Nat)
    (z : ContinuousTwoCocycle (G := G) (A := A n) (action := actn n))
    (hz : QuotientGroup.mk z =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n)
    (w : ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1)))
    (hw : QuotientGroup.mk w =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) (n+1)) :
    ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1)) :=
  w * deltaOneCocycle (actn (n+1))
    (liftCochain A proj hproj n
      (corrCochain A proj actn compat n
        (Classical.choose (exists_defect A proj actn compat y n z hz w hw))))

theorem correctNext_class (hproj : ∀ n, Function.Surjective (proj n))
    (y : LimH2 A proj actn compat) (n : Nat)
    (z : ContinuousTwoCocycle (G := G) (A := A n) (action := actn n))
    (hz : QuotientGroup.mk z =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n)
    (w : ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1)))
    (hw : QuotientGroup.mk w =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) (n+1)) :
    QuotientGroup.mk (correctNext A proj actn compat hproj y n z hz w hw) =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) (n+1) := by
  rw [correctNext, mk_mul_deltaOneCocycle, hw]

theorem correctNext_proj (hproj : ∀ n, Function.Surjective (proj n))
    (y : LimH2 A proj actn compat) (n : Nat)
    (z : ContinuousTwoCocycle (G := G) (A := A n) (action := actn n))
    (hz : QuotientGroup.mk z =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n)
    (w : ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1)))
    (hw : QuotientGroup.mk w =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) (n+1)) :
    twoCocycleProj A proj actn compat n (correctNext A proj actn compat hproj y n z hz w hw) = z := by
  have hdef := Classical.choose_spec (exists_defect A proj actn compat y n z hz w hw)
  rw [correctNext, map_mul, hdef, deltaOneCocycle_twoCocycleProj,
    liftCochain_spec, corrCochain_spec]
  group

/-- The state of the recursion: a level n 2-cocycle representing the level class
y n. -/
abbrev RepState (y : LimH2 A proj actn compat) (n : Nat) : Type u :=
  {z : ContinuousTwoCocycle (G := G) (A := A n) (action := actn n) //
    QuotientGroup.mk z =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n}

/-- The corrected representative at every level, built by recursion. -/
noncomputable def repState (hproj : ∀ n, Function.Surjective (proj n))
    (y : LimH2 A proj actn compat) (n : Nat) : RepState A proj actn compat y n :=
  Nat.rec (motive := fun n => RepState A proj actn compat y n)
    ⟨levelRep A proj actn compat y 0, levelRep_mk A proj actn compat y 0⟩
    (fun n prev =>
      ⟨correctNext A proj actn compat hproj y n prev.1 prev.2
          (levelRep A proj actn compat y (n+1)) (levelRep_mk A proj actn compat y (n+1)),
        correctNext_class A proj actn compat hproj y n prev.1 prev.2
          (levelRep A proj actn compat y (n+1)) (levelRep_mk A proj actn compat y (n+1))⟩)
    n

/-- The level n cocycle of the corrected family. -/
noncomputable def repCocycle (hproj : ∀ n, Function.Surjective (proj n))
    (y : LimH2 A proj actn compat) (n : Nat) :
    ContinuousTwoCocycle (G := G) (A := A n) (action := actn n) :=
  (repState A proj actn compat hproj y n).1

theorem repCocycle_class (hproj : ∀ n, Function.Surjective (proj n))
    (y : LimH2 A proj actn compat) (n : Nat) :
    QuotientGroup.mk (repCocycle A proj actn compat hproj y n) =
      (y : ∀ k, ContinuousH2 (G := G) (A := A k) (action := actn k)) n :=
  (repState A proj actn compat hproj y n).2

/-- The corrected family is compatible under the level projections. -/
theorem repCocycle_compat (hproj : ∀ n, Function.Surjective (proj n))
    (y : LimH2 A proj actn compat) (n : Nat) :
    twoCocycleProj A proj actn compat n
      (repCocycle A proj actn compat hproj y (n+1)) =
      repCocycle A proj actn compat hproj y n := by
  have hstep : repCocycle A proj actn compat hproj y (n+1) =
      correctNext A proj actn compat hproj y n
        (repCocycle A proj actn compat hproj y n)
        (repCocycle_class A proj actn compat hproj y n)
        (levelRep A proj actn compat y (n+1)) (levelRep_mk A proj actn compat y (n+1)) := rfl
  rw [hstep]
  exact correctNext_proj A proj actn compat hproj y n _ _ _ _

/-- **Surjectivity of the degree-two comparison from coefficient surjectivity.**
This is the compatible representative theorem: every compatible family of level
H^2 classes is represented by a continuous 2-cocycle of the inverse limit. -/
theorem h2Comparison_surjective_of_coeff_surjective
    (hproj : ∀ n, Function.Surjective (proj n)) :
    Function.Surjective (h2Comparison A proj actn compat) := by
  intro y
  have hcompat : ∀ n, twoCochainProj A proj n
      ((repCocycle A proj actn compat hproj y (n+1) :
          ContinuousTwoCocycle (G := G) (A := A (n+1)) (action := actn (n+1))) :
        ContinuousTwoCochain (G := G) (A := A (n+1))) =
      ((repCocycle A proj actn compat hproj y n :
          ContinuousTwoCocycle (G := G) (A := A n) (action := actn n)) :
        ContinuousTwoCochain (G := G) (A := A n)) := by
    intro n
    rw [← twoCocycleProj_apply, repCocycle_compat]
  let climb : ContinuousTwoCochain (G := G) (A := LimCoeff A proj) :=
    limitCochain A proj
      (fun n => ((repCocycle A proj actn compat hproj y n :
        ContinuousTwoCocycle (G := G) (A := A n) (action := actn n)) :
          ContinuousTwoCochain (G := G) (A := A n))) hcompat
  have hmem : climb ∈ twoCocycleSubgroup (action := limitAction A proj actn compat) := by
    rw [mem_twoCocycle_iff_levels A proj actn compat]
    intro n
    rw [twoCochainLevel_limitCochain]
    exact (repCocycle A proj actn compat hproj y n).2
  let c : ContinuousTwoCocycle (G := G) (A := LimCoeff A proj)
      (action := limitAction A proj actn compat) := ⟨climb, hmem⟩
  refine ⟨QuotientGroup.mk c, ?_⟩
  rw [h2Comparison_mk]
  apply Subtype.ext
  funext n
  rw [z2ToLimH2_apply]
  have hzone : twoCocycleLevel A proj actn compat n c = repCocycle A proj actn compat hproj y n := by
    apply Subtype.ext
    rw [twoCocycleLevel_apply]
    exact twoCochainLevel_limitCochain A proj _ _ n
  rw [hzone]
  exact repCocycle_class A proj actn compat hproj y n

/-- The compatible representative lift of S2114 exists whenever the coefficient
transitions are surjective. -/
noncomputable def representativeLift_of_coeff_surjective
    (hproj : ∀ n, Function.Surjective (proj n)) :
    S2114CompatibleRepresentativeLift A proj actn compat :=
  Classical.choice (S2114_representativeLift_of_surjective A proj actn compat
    (h2Comparison_surjective_of_coeff_surjective A proj actn compat hproj))

/-- **S2114, reused**: a compatible representative lift yields surjectivity of the
comparison. -/
theorem surjective_of_representativeLift
    (L : S2114CompatibleRepresentativeLift A proj actn compat) :
    Function.Surjective (h2Comparison A proj actn compat) :=
  S2114_surjective_of_representativeLift A proj actn compat L

/-- **S2114, reused**: surjectivity and a compatible representative lift are
equivalent. -/
theorem nonempty_representativeLift_iff_surjective :
    Nonempty (S2114CompatibleRepresentativeLift A proj actn compat) ↔
      Function.Surjective (h2Comparison A proj actn compat) :=
  ⟨fun ⟨L⟩ => S2114_surjective_of_representativeLift A proj actn compat L,
    fun h => S2114_representativeLift_of_surjective A proj actn compat h⟩

/-- Surjectivity of the comparison is the S2114 statement. -/
theorem h2ComparisonSurjective_iff_s2114 :
    S2114H2ComparisonSurjective A proj actn compat ↔
      Function.Surjective (h2Comparison A proj actn compat) :=
  Iff.rfl

/-- **The degree-two exchange from coefficient surjectivity and the lim^1 H^1
input.**  The lim^1 input is exactly S2112's coboundary lift (injectivity of the
comparison). -/
theorem bijective_of_coeff_surjective_of_coboundaryLift
    (hproj : ∀ n, Function.Surjective (proj n))
    (hl : CoboundaryLift A proj actn compat) :
    Function.Bijective (h2Comparison A proj actn compat) :=
  bijective_of_coboundaryLift_of_surjective A proj actn compat hl
    (h2Comparison_surjective_of_coeff_surjective A proj actn compat hproj)

end Representative

/-! ## 4. The lim^1 H^1 input: level 1-cocycles and the H^1 tower -/

section H1Input

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Nat → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)
variable (actn : ∀ n, Iut.ContinuousGroupAction G (A n))
variable (compat : ∀ n (g : G) (x : A (n+1)),
  proj n ((actn (n+1)).act g x) = (actn n).act g (proj n x))

/-- Level-n continuous 1-cocycles, i.e. the kernel of the first differential. -/
abbrev LevelOneCocycle (n : Nat) : Subgroup (ContinuousOneCochain (G := G) (A := A n)) :=
  (deltaOne (actn n)).ker

/-- The level projection of continuous 1-cocycles. -/
noncomputable def oneCocycleProj (n : Nat) :
    LevelOneCocycle A actn (n+1) →* LevelOneCocycle A actn n where
  toFun a :=
    ⟨oneCochainProj A proj n a.1, by
      rw [MonoidHom.mem_ker]
      rw [← deltaOne_twoCochainProj A proj actn compat n a.1, MonoidHom.mem_ker.mp a.2]
      simp⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (oneCochainProj A proj n)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (oneCochainProj A proj n) a.1 b.1

/-- **The lim^1 H^1 input, in cocycle form**: the level transitions on continuous
1-cocycles are surjective.  This is the input under which the coboundary lift
(hence injectivity of the H^2 comparison) is expected; no inhabitant is asserted
here. -/
def OneCocycleProjSurjective : Prop :=
  ∀ n, Function.Surjective (oneCocycleProj A proj actn compat n)

/-- The level H^1 tower of S2138 attached to the coefficient system, given the
finiteness of the level H^1 groups and their transition maps. -/
noncomputable def levelH1Tower (hfin : ∀ n, Finite (Iut.ContinuousH1 (actn n)))
    (projH1 : ∀ n, Iut.ContinuousH1 (actn (n+1)) →* Iut.ContinuousH1 (actn n)) :
    S2138H1Tower where
  H1 := fun n => Iut.ContinuousH1 (actn n)
  commGroup := fun n => inferInstance
  finite := hfin
  proj := projH1

/-- **The lim^1 H^1 input in the Mittag-Leffler form of S2138.**  Once the level
transitions of the H^1 tower are surjective, the tower satisfies the
Mittag-Leffler condition, which is the vanishing of lim^1 for the H^1 system. -/
theorem levelH1Tower_mittagLeffler
    (hfin : ∀ n, Finite (Iut.ContinuousH1 (actn n)))
    (projH1 : ∀ n, Iut.ContinuousH1 (actn (n+1)) →* Iut.ContinuousH1 (actn n))
    (hsurj : ∀ n, Function.Surjective (projH1 n)) :
    S2138MittagLeffler (levelH1Tower A actn hfin projH1) :=
  S2138MittagLeffler_of_surjective (levelH1Tower A actn hfin projH1) hsurj

end H1Input

/-! ## 5. The actual arithmetic tower: mu_{n!}, its power transitions and the
compatible action of the local absolute Galois group -/

section Actual

open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The actual coefficient transition mu_{(n+1)!} -> mu_{n!}, zeta |-> zeta^(n+1),
is surjective: every root of unity omega of order dividing n! has an (n+1)-st
root in the algebraic closure, which is again a root of unity of order dividing
(n+1)!. -/
theorem S2427PowMap_surjective (n : Nat) : Function.Surjective (S2145PowMap p n) := by
  intro om
  obtain ⟨x, hx⟩ :=
    IsAlgClosed.exists_pow_nat_eq (om.1 : AlgebraicClosure ℚ_[p]) (Nat.succ_pos n)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.succ_ne_zero n)] at hx
    exact (Units.ne_zero om.1) hx.symm
  let u : (AlgebraicClosure ℚ_[p])ˣ := Units.mk0 x hx0
  have hu : u ^ (n+1) = om.1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hx
  have hmem : u ^ Nat.factorial (n+1) = 1 := by
    rw [Nat.factorial_succ, pow_mul, hu]
    have hom : om.1 ^ Nat.factorial n = 1 :=
      (mem_rootsOfUnity (Nat.factorial n) (AlgebraicClosure ℚ_[p])).mp om.2
    exact hom
  refine ⟨⟨u, hmem⟩, ?_⟩
  apply Subtype.ext
  exact hu

/-- The coefficient transitions of the actual mu_{n!} tower are surjective. -/
theorem S2427ActualCoeffTransition_surjective :
    ∀ n, Function.Surjective (S2145PowMap p n) :=
  fun n => S2427PowMap_surjective p n

/-- **The actual H^2 comparison is surjective**: every compatible family of level
H^2 classes of the mu_{n!} tower is represented by a continuous 2-cocycle of the
inverse limit. -/
theorem S2427ActualH2Comparison_surjective :
    Function.Surjective
      (h2Comparison (A := S2145Coeff p) (proj := S2145PowMap p)
        (actn := (S2196MuActionTower p).actn)
        (compat := (S2196MuActionTower p).compat)) :=
  h2Comparison_surjective_of_coeff_surjective _ _ _ _
    (S2427ActualCoeffTransition_surjective p)

/-- **The actual compatible representative**: a lift of compatible families of
level H^2 classes of the mu_{n!} tower through the H^2 projection tower. -/
noncomputable def S2427ActualRepresentativeLift :
    S2114CompatibleRepresentativeLift (S2145Coeff p) (S2145PowMap p)
      (S2196MuActionTower p).actn (S2196MuActionTower p).compat :=
  representativeLift_of_coeff_surjective _ _ _ _
    (S2427ActualCoeffTransition_surjective p)

/-- The S2114 surjectivity statement for the actual tower. -/
theorem S2427ActualS2114Surjective :
    S2114H2ComparisonSurjective (S2145Coeff p) (S2145PowMap p)
      (S2196MuActionTower p).actn (S2196MuActionTower p).compat :=
  S2427ActualH2Comparison_surjective p

/-- **Exact remaining input for the actual degree-two exchange.**  Surjectivity is
unconditional; injectivity is, by S2112, exactly the coboundary lift, i.e. the
lim^1-vanishing of the level H^1 system.  No inhabitant is asserted. -/
def S2427ActualH2ExchangeInput : Prop :=
  CoboundaryLift (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat

/-- The actual degree-two exchange, conditional on the lim^1 H^1 input. -/
theorem S2427ActualH2Comparison_bijective
    (hl : S2427ActualH2ExchangeInput p) :
    Function.Bijective
      (h2Comparison (A := S2145Coeff p) (proj := S2145PowMap p)
        (actn := (S2196MuActionTower p).actn)
        (compat := (S2196MuActionTower p).compat)) :=
  bijective_of_coeff_surjective_of_coboundaryLift _ _ _ _
    (S2427ActualCoeffTransition_surjective p) hl

end Actual

/-! ## 6. Axiom probes -/

#print axioms oneCochainProj_surjective
#print axioms limitCochain
#print axioms twoCochainLevel_limitCochain
#print axioms twoCochainProj_twoCochainLevel
#print axioms mk_mul_deltaOneCocycle
#print axioms exists_defect
#print axioms exists_neg_delta
#print axioms correctNext_class
#print axioms correctNext_proj
#print axioms repCocycle_compat
#print axioms h2Comparison_surjective_of_coeff_surjective
#print axioms representativeLift_of_coeff_surjective
#print axioms nonempty_representativeLift_iff_surjective
#print axioms bijective_of_coeff_surjective_of_coboundaryLift
#print axioms oneCocycleProj
#print axioms levelH1Tower_mittagLeffler
#print axioms S2427PowMap_surjective
#print axioms S2427ActualH2Comparison_surjective
#print axioms S2427ActualRepresentativeLift
#print axioms S2427ActualH2Comparison_bijective

end LeanFormal.IUT.XiFPaper.S2427H2CompatRepActual
