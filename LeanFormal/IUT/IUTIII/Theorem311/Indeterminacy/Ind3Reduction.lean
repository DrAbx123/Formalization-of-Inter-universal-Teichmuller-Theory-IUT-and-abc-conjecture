import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.UpperSemi
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-!
# Ind3 upper-semi compatibility: shape-level reduction

Frozen target `IUT-III.Ind3` (IUTIII/Theorem311/Indeterminacy/Ind3.lean):
"Construct and prove upper-semi compatibility, not just state it."

Source location of the assertion.

* IUT III, Theorem 3.11, (ii), the `(Ind3)` paragraph (physical page 156 of the
  paper; corpus extract
  `papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_through_Corollary312_pp153-186.plain.txt`,
  lines 302--309):
  "(Ind3) as one varies m in Z, the isomorphisms of (a) are `upper semi-compatible`,
  relative to the log-links of the n-th column of the LGP-Gaussian log-theta-lattice
  under consideration, in a sense that involves certain natural inclusions `⊆` at
  v_Q in V^non_Q and certain natural surjections `↠` at v_Q in V^arc_Q ---
  cf. Proposition 3.5, (ii), (a), (b), for more details."
* IUT III, Proposition 3.5, (ii), (a) (Nonarchimedean Primes; printed pages 104--105):
  the topological module I(S^+-_{j+1} F(n,circ-D)_{v_Q}) contains the images of the
  Galois-invariant submodules of the unit groups, over V contains v | v_Q and
  |t| in {0,...,j}, both via (1) the tensor product of the Kummer isomorphisms and
  (2) the tensor product of their pre-composites with the m'-th log-link iterates
  for m' >= 1.
* IUT III, Proposition 3.5, (ii), (b) (Archimedean Primes; printed pages 105--106):
  the closed unit ball contains the image, via the Kummer tensor product, of the unit
  groups and of the closed balls of radius pi; and it contains, for each m' >= 1, a
  subset that surjects, via the m'-th log-link iterate, onto the unit subset on which
  the iterate is defined.
* ELSIUT: the `(Ind3)` discussion ("interpreting this failure to commute as a sort of
  `upper semi-commutativity`"), the label `(CnfInd3)` ("restrict one's attention to
  upper bounds [i.e., but not lower bounds!]"), and the label `(ExtInd1)`
  ("the upper semi-continuity of (Ind3)").

This file is a reduction form, explicitly not a substitute for the source assertion.
It proves the order-theoretic skeleton used by the `(Ind3)` comparison: the
one-sided dominance preorder on possible images of a Theta-pilot object, its relation
to the existing `UpperSemiCorrespondence` kernel, the two source mechanisms
(`⊆` containment into the vertically coric module; `↠` surjective covers by the
log-link iterates), the assembly over tensor factors and places, and the bridge to
the `VerticalLogKummerCorrespondence` contract of IUT II. The construction of the
actual analytic carriers (log-shell tensor packets, Kummer isomorphisms, log-links)
is not available in the current repository; the source instance remains the open
card recorded in `logs/coordination/ind3-reduction-20261016.md`.
-/

noncomputable section

namespace LeanFormal.IUT

universe u v w

/-- A possible image of a Theta-pilot object at a fixed stage, i.e. a set of values
of the target of a Kummer comparison; compare IUT III, Definition 3.8, (i), and the
notion of "possible images" used in Theorem 3.11, (i), (a). -/
structure PossibleImage (β : Type v) [Preorder β] where
  carrier : Set β

namespace PossibleImage

variable {β : Type v} [Preorder β]

instance instMembership : Membership β (PossibleImage β) where
  mem := fun φ z => z ∈ φ.carrier

/-- The one-sided dominance preorder: every value of the left image is dominated,
inside the right image, by a value of the right image.  This is the upper-semi
comparison of `(Ind3)` at the level of possible images: one-sided, in contrast to
a precise equality. -/
instance instPreorder : Preorder (PossibleImage β) where
  le φ ψ := ∀ z ∈ φ, ∃ w ∈ ψ, z ≤ w
  le_refl := fun φ z hz => ⟨z, hz, le_rfl⟩
  le_trans := fun φ ψ χ hφψ hψχ z hz => by
    obtain ⟨w, hw, hzw⟩ := hφψ z hz
    obtain ⟨x, hx, hwx⟩ := hψχ w hw
    exact ⟨x, hx, le_trans hzw hwx⟩

@[ext] theorem ext {φ ψ : PossibleImage β} (h : ∀ z, z ∈ φ ↔ z ∈ ψ) :
    φ = ψ := by
  rcases φ with ⟨cφ⟩
  rcases ψ with ⟨cψ⟩
  exact congrArg PossibleImage.mk (Set.ext h)

/-- Membership bridge: the class instance is the carrier membership. -/
@[simp] theorem mem_carrier {z : β} {φ : PossibleImage β} :
    z ∈ φ ↔ z ∈ φ.carrier := Iff.rfl

theorem le_def {φ ψ : PossibleImage β} :
    φ ≤ ψ ↔ ∀ z ∈ φ, ∃ w ∈ ψ, z ≤ w := Iff.rfl

/-- Set inclusion into the right image is the nonarchimedean containment reading of
the upper-semi comparison: it implies dominance through reflexivity. -/
theorem subset_le {φ ψ : PossibleImage β} (h : φ.carrier ⊆ ψ.carrier) : φ ≤ ψ :=
  fun z hz => ⟨z, h hz, le_rfl⟩

/-- The downward closure of a possible image: all values dominated by some value of
the image.  In the upper-bound reading of the label `(CnfInd3)`, admissible values
are exactly those bounded above by the Kummer image, so the relevant possible
images are down-closed. -/
def lowerClosure (φ : PossibleImage β) : PossibleImage β where
  carrier := {z | ∃ w ∈ φ, z ≤ w}

@[simp] theorem mem_lowerClosure {z : β} {φ : PossibleImage β} :
    z ∈ lowerClosure φ ↔ ∃ w ∈ φ, z ≤ w := Iff.rfl

theorem le_lowerClosure (φ : PossibleImage β) : φ ≤ lowerClosure φ :=
  fun z hz => ⟨z, ⟨z, hz, le_rfl⟩, le_rfl⟩

theorem lowerClosure_monotone :
    Monotone (lowerClosure : PossibleImage β → PossibleImage β) := by
  intro φ ψ hφψ z hz
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨w', hw', hww'⟩ := hφψ w hw
  exact ⟨w', ⟨w', hw', le_rfl⟩, le_trans hzw hww'⟩

theorem lowerClosure_idem (φ : PossibleImage β) :
    lowerClosure (lowerClosure φ) = lowerClosure φ := by
  apply ext
  intro z
  constructor
  · intro hz
    rw [mem_lowerClosure] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    rw [mem_lowerClosure] at hw
    obtain ⟨w0, hw0, hw0w⟩ := hw
    rw [mem_lowerClosure]
    exact ⟨w0, hw0, le_trans hzw hw0w⟩
  · intro hz
    rw [mem_lowerClosure] at hz
    obtain ⟨w0, hw0, hzw0⟩ := hz
    rw [mem_lowerClosure]
    exact ⟨w0, ⟨w0, hw0, le_rfl⟩, hzw0⟩

/-- A down-closed possible image: closed under going down in the order. -/
def IsLowerClosed (φ : PossibleImage β) : Prop :=
  ∀ ⦃z w : β⦄, w ∈ φ → z ≤ w → z ∈ φ

theorem lowerClosure_isLowerClosed (φ : PossibleImage β) :
    IsLowerClosed (lowerClosure φ) := by
  intro z w hw hzw
  rw [mem_lowerClosure] at hw
  obtain ⟨w0, hw0, ww0⟩ := hw
  rw [mem_lowerClosure]
  exact ⟨w0, hw0, le_trans hzw ww0⟩

/-- On down-closed possible images the upper-semi comparison is precisely set
inclusion: the one-sided inclusions of the source, as opposed to precise equalities. -/
theorem le_iff_carrier_subset_of_isLowerClosed {φ ψ : PossibleImage β}
    (hψ : IsLowerClosed ψ) : φ ≤ ψ ↔ φ.carrier ⊆ ψ.carrier := by
  constructor
  · intro h z hz
    obtain ⟨w, hw, hzw⟩ := h z hz
    exact hψ hw hzw
  · intro h z hz
    exact ⟨z, h hz, le_rfl⟩

/-- The downward closure is left adjoint to the inclusion of down-closed images:
closing the source of a comparison does not change which comparisons hold. -/
theorem lowerClosure_le_iff {φ ψ : PossibleImage β} :
    lowerClosure φ ≤ ψ ↔ φ ≤ ψ := by
  constructor
  · intro h z hz
    exact h z ⟨z, hz, le_rfl⟩
  · intro h z hz
    rw [mem_lowerClosure] at hz
    obtain ⟨w0, hw0, zw0⟩ := hz
    obtain ⟨w, hw, w0w⟩ := h w0 hw0
    exact ⟨w, hw, le_trans zw0 w0w⟩

/-- The tensor product of possible images over an index family (the tensor product
over |t| in {0,...,j} and the product over the places V contains v | v_Q of
Proposition 3.5, (ii), (a), (b)): a tuple of values is possible when each component
is possible. -/
def pi {ι : Type u} {β : ι → Type v} [∀ i, Preorder (β i)]
    (Φ : ∀ i, PossibleImage (β i)) : PossibleImage (∀ i, β i) where
  carrier := {w | ∀ i, w i ∈ Φ i}

theorem pi_le_pi_iff {ι : Type u} {β : ι → Type v} [∀ i, Preorder (β i)]
    {Φ Ψ : ∀ i, PossibleImage (β i)}
    (hne : ∀ i, (Φ i).carrier.Nonempty) :
    pi Φ ≤ pi Ψ ↔ ∀ i, Φ i ≤ Ψ i := by
  constructor
  · intro h i z hz
    classical
    choose z' hz' using hne
    let tuple : ∀ j, β j := Function.update z' i z
    have htuple : tuple ∈ pi Φ := by
      change ∀ j, tuple j ∈ Φ j
      intro j
      by_cases hj : j = i
      · subst hj
        simpa [tuple] using hz
      · simpa [tuple, Function.update, hj, mem_carrier] using hz' j
    obtain ⟨w, hw, htw⟩ := h tuple htuple
    refine ⟨w i, hw i, ?_⟩
    simpa [tuple] using htw i
  · intro h z hz
    change ∀ j, z j ∈ Φ j at hz
    choose w hw using fun i => h i (z i) (hz i)
    exact ⟨w, fun i => (hw i).1, fun i => (hw i).2⟩

/-- The union (the "totality", as m ranges over the column) of a family of possible
images. -/
def iUnion {ι : Type u} (Φ : ι → PossibleImage β) : PossibleImage β where
  carrier := {z | ∃ i, z ∈ Φ i}

@[simp] theorem mem_iUnion {z : β} {ι : Type u} {Φ : ι → PossibleImage β} :
    z ∈ iUnion Φ ↔ ∃ i, z ∈ Φ i := Iff.rfl

theorem le_iUnion {ι : Type u} (Φ : ι → PossibleImage β) (i : ι) :
    Φ i ≤ iUnion Φ :=
  fun z hz => ⟨z, ⟨i, hz⟩, le_rfl⟩

theorem iUnion_le {ι : Type u} {Φ : ι → PossibleImage β} {Ψ : PossibleImage β} :
    iUnion Φ ≤ Ψ ↔ ∀ i, Φ i ≤ Ψ := by
  constructor
  · intro h i z hz
    exact h z ⟨i, hz⟩
  · intro h z hz
    rw [mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    exact h i z hi

end PossibleImage

/-- The archimedean surjection mechanism of Proposition 3.5, (ii), (b): every value
of the left possible image is the image, under the comparison map sigma, of a value
of the right possible image (the m'-th log-link iterate surjects onto the unit
subset on which it is defined). -/
def SurjectionCovers {β : Type v} [Preorder β] (σ : β → β)
    (φ ψ : PossibleImage β) : Prop :=
  ∀ z ∈ φ, ∃ w ∈ ψ, σ w = z

/-- The identity comparison is the containment reading: the nonarchimedean
mechanism is the special case sigma = id of the surjective-cover mechanism. -/
theorem surjectionCovers_id_iff {β : Type v} [Preorder β] {φ ψ : PossibleImage β} :
    SurjectionCovers id φ ψ ↔ φ.carrier ⊆ ψ.carrier := by
  constructor
  · intro h z hz
    obtain ⟨w, hw, hwz⟩ := h z hz
    have hwz' : w = z := by simpa using hwz
    rw [hwz'] at hw
    simpa [PossibleImage.mem_carrier] using hw
  · intro h z hz
    exact ⟨z, h hz, rfl⟩

/-- Surjective covers compose: the pre-composites of the Kummer isomorphisms with
log-link iterates compose with one another. -/
theorem surjectionCovers_comp {β : Type v} [Preorder β] {σ τ : β → β}
    {φ ψ χ : PossibleImage β} (h1 : SurjectionCovers σ φ ψ)
    (h2 : SurjectionCovers τ ψ χ) : SurjectionCovers (σ ∘ τ) φ χ := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := h1 z hz
  obtain ⟨x, hx, hxw⟩ := h2 w hw
  exact ⟨x, hx, by rw [Function.comp_apply, hxw, hwz]⟩

/-- A surjective cover discharges the upper-semi dominance comparison as soon as
the comparison map raises values into their preimages: the surjection mechanism of
the archimedean clause. -/
theorem le_of_surjectionCovers {β : Type v} [Preorder β] {σ : β → β}
    {φ ψ : PossibleImage β} (hσ : ∀ w z, σ w = z → z ≤ w)
    (h : SurjectionCovers σ φ ψ) : φ ≤ ψ :=
  fun z hz => by
    obtain ⟨w, hw, hwz⟩ := h z hz
    exact ⟨w, hw, hσ w z hwz⟩

/-- The upper-semi law for a family of possible images: monotonicity in the
one-sided dominance preorder. -/
def IsUpperSemi {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (F : α → PossibleImage β) : Prop :=
  Monotone F

/-- The upper-semi law, spelled out in the shape used by the existing
`UpperSemiCorrespondence` kernel. -/
theorem isUpperSemi_iff {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (F : α → PossibleImage β) :
    IsUpperSemi F ↔ ∀ ⦃x y : α⦄, x ≤ y → ∀ z ∈ F x, ∃ w ∈ F y, z ≤ w :=
  Iff.rfl

/-- The nonarchimedean containment mechanism in family form: a stage family whose
images are monotone by set inclusion is upper-semi.  This is the containment
reading of Proposition 3.5, (ii), (a). -/
theorem isUpperSemi_of_carrier_monotone {α : Type u} {β : Type v}
    [Preorder α] [Preorder β] {F : α → PossibleImage β}
    (h : Monotone (fun a => (F a).carrier)) : IsUpperSemi F :=
  fun x y hxy z hz => ⟨z, h hxy hz, le_rfl⟩

/-- The tensor assembly of Proposition 3.5, (ii), (a), (b): an index family whose
factors are upper-semi is upper-semi for the product possible-image family. -/
theorem isUpperSemi_pi {α : Type w} {ι : Type u} {β : ι → Type v}
    [Preorder α] [∀ i, Preorder (β i)]
    (F : α → ∀ i, PossibleImage (β i))
    (hF : ∀ i, IsUpperSemi (fun a => F a i)) :
    IsUpperSemi (fun a => PossibleImage.pi (F a)) := by
  intro x y hxy z hz
  choose w hw using fun i => hF i hxy (z i) (hz i)
  exact ⟨w, fun i => (hw i).1, fun i => (hw i).2⟩

namespace UpperSemiCorrespondence

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

/-- Every upper-semi correspondence is a monotone possible-image family. -/
theorem isUpperSemi (C : UpperSemiCorrespondence α β) :
    IsUpperSemi (fun a => (⟨C.image a⟩ : PossibleImage β)) :=
  fun x y hxy z hz => C.upper hxy z hz

/-- Conversely, every monotone possible-image family is an upper-semi
correspondence. -/
def ofIsUpperSemi (F : α → PossibleImage β) (hF : IsUpperSemi F) :
    UpperSemiCorrespondence α β where
  image a := (F a).carrier
  upper := fun {x y} hxy z hz => hF hxy z hz

@[simp] theorem ofIsUpperSemi_image (F : α → PossibleImage β)
    (hF : IsUpperSemi F) (a : α) :
    (ofIsUpperSemi F hF).image a = (F a).carrier := rfl

end UpperSemiCorrespondence

namespace VerticalLogKummerCorrespondence

variable (K : VerticalLogKummerCorrespondence)

/-- The singleton possible-image family of the Kummer images along the iterated
log-links of the n-th column, starting at stage m0. -/
def imageFamily (m0 : ℕ) (x : K.F m0) : ℕ → PossibleImage K.D :=
  fun n => ⟨{K.kummer (m0 + n) (K.transport m0 n x)}⟩

theorem imageFamily_le_succ (m0 : ℕ) (x : K.F m0) (n : ℕ) :
    K.imageFamily m0 x n ≤ K.imageFamily m0 x (n + 1) := by
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  refine ⟨K.kummer (m0 + (n + 1)) (K.transport m0 (n + 1) x),
    Set.mem_singleton _, ?_⟩
  exact K.upperSemi (m0 + n) (K.transport m0 n x)

/-- The upper-semi law for the Kummer images along the iterated log-links: the
one-step inclusion `upperSemi` of the IUT-II contract iterates. -/
theorem imageFamily_monotone (m0 : ℕ) (x : K.F m0) :
    Monotone (K.imageFamily m0 x) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (K.imageFamily_le_succ m0 x k)

/-- The vertically coric hull, once it dominates the transported Kummer images,
dominates the whole possible-image family. -/
theorem hull_dominates_imageFamily {x0 : K.F 0} {hull : K.D}
    (h : K.HullDominates x0 hull) (n : ℕ) :
    K.imageFamily 0 x0 n ≤ (⟨{hull}⟩ : PossibleImage K.D) := by
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact ⟨hull, Set.mem_singleton _, h n⟩

end VerticalLogKummerCorrespondence

/-! ## The conditional contract for the Proposition 3.5, (ii) clauses -/

/-- Reduction-form carrier of the upper-semi compatibility clauses of IUT III,
Proposition 3.5, (ii), (a) and (b), for one place v_Q and one tensor-packet layer:

* `kummerImage m` is the (tensor product of the) Kummer images of the stage-m
  labeled data in the vertically coric module, and `iterateImage m n` is the image
  of the pre-composites of the Kummer isomorphisms with the (n+1)-st log-link
  iterates (the source index m' >= 1 is reindexed by n : ℕ, m' = n + 1);
* `coricModule` is the vertically coric module which, by clause (a), contains the
  images of `kummerImage` and of `iterateImage`;
* `archBall m`, `unitImage m`, `piBallImage m`, and `logIterate m n` are the
  archimedean counterparts of clause (b): the closed unit ball contains the Kummer
  images of the units and of the closed balls of radius pi, and, for each m' >= 1,
  contains a subset that surjects, via the m'-th log-link iterate, onto the unit
  subset on which the iterate is defined (`iterateDefinedUnits`).

The fields are the frozen source clauses at the level of possible images; their
instantiation for the actual analytic carriers is the open source instance. -/
structure LogKummerUpperSemiData (β : Type v) [Preorder β] where
  kummerImage : ℤ → PossibleImage β
  iterateImage : ℤ → ℕ → PossibleImage β
  coricModule : PossibleImage β
  kummer_subset_coric : ∀ m : ℤ, (kummerImage m).carrier ⊆ coricModule.carrier
  iterate_subset_coric : ∀ (m : ℤ) (n : ℕ),
    (iterateImage m n).carrier ⊆ coricModule.carrier
  archBall : ℤ → PossibleImage β
  unitImage : ℤ → PossibleImage β
  piBallImage : ℤ → PossibleImage β
  unit_in_ball : ∀ m : ℤ, (unitImage m).carrier ⊆ (archBall m).carrier
  piBall_in_ball : ∀ m : ℤ, (piBallImage m).carrier ⊆ (archBall m).carrier
  logIterate : ℤ → ℕ → β → β
  iterateDefinedUnits : ℤ → ℕ → PossibleImage β
  arch_surjects : ∀ (m : ℤ) (n : ℕ),
    SurjectionCovers (logIterate m n) (iterateDefinedUnits m n) (archBall m)

namespace LogKummerUpperSemiData

variable {β : Type v} [Preorder β]

/-- Clause (a), Kummer route: the coric module dominates the stage-m Kummer image
in the one-sided comparison preorder. -/
theorem kummer_le_coric (D : LogKummerUpperSemiData β) (m : ℤ) :
    D.kummerImage m ≤ D.coricModule :=
  PossibleImage.subset_le (D.kummer_subset_coric m)

theorem iterate_le_coric (D : LogKummerUpperSemiData β) (m : ℤ) (n : ℕ) :
    D.iterateImage m n ≤ D.coricModule :=
  PossibleImage.subset_le (D.iterate_subset_coric m n)

theorem unit_le_ball (D : LogKummerUpperSemiData β) (m : ℤ) :
    D.unitImage m ≤ D.archBall m :=
  PossibleImage.subset_le (D.unit_in_ball m)

theorem piBall_le_ball (D : LogKummerUpperSemiData β) (m : ℤ) :
    D.piBallImage m ≤ D.archBall m :=
  PossibleImage.subset_le (D.piBall_in_ball m)

/-- The totality of the log-link-iterate routes at a fixed stage, i.e. the union
over all m' >= 1 (reindexed by ℕ) of `iterateImage`. -/
def iterateTotality (D : LogKummerUpperSemiData β) (m : ℤ) : PossibleImage β :=
  PossibleImage.iUnion (fun n : ℕ => D.iterateImage m n)

theorem iterate_le_iterateTotality (D : LogKummerUpperSemiData β) (m : ℤ)
    (n : ℕ) : D.iterateImage m n ≤ D.iterateTotality m :=
  PossibleImage.le_iUnion (fun n : ℕ => D.iterateImage m n) n

/-- Clause (a) assembled over the totality of iterates: the coric module is an
upper bound for every pre-composite route. -/
theorem iterateTotality_le_coric (D : LogKummerUpperSemiData β) (m : ℤ) :
    D.iterateTotality m ≤ D.coricModule :=
  PossibleImage.iUnion_le.mpr (fun n => D.iterate_le_coric m n)

theorem arch_surjection_cover (D : LogKummerUpperSemiData β) (m : ℤ) (n : ℕ) :
    SurjectionCovers (D.logIterate m n) (D.iterateDefinedUnits m n)
      (D.archBall m) :=
  D.arch_surjects m n

/-- Reduction form of IUT III, Theorem 3.11, (ii), `(Ind3)`, at the level of the
clauses of Proposition 3.5, (ii): the nonarchimedean containment routes all land
under the coric module, and the archimedean surjective covers compare the stage-m
balls with the defined unit subsets. -/
theorem upperSemi_reduction (D : LogKummerUpperSemiData β) :
    (∀ m : ℤ, D.kummerImage m ≤ D.coricModule) ∧
    (∀ m : ℤ, D.iterateTotality m ≤ D.coricModule) ∧
    (∀ m : ℤ, D.unitImage m ≤ D.archBall m) ∧
    (∀ m : ℤ, D.piBallImage m ≤ D.archBall m) ∧
    (∀ (m : ℤ) (n : ℕ),
      SurjectionCovers (D.logIterate m n) (D.iterateDefinedUnits m n)
        (D.archBall m)) :=
  ⟨D.kummer_le_coric, D.iterateTotality_le_coric, D.unit_le_ball,
    D.piBall_le_ball, D.arch_surjection_cover⟩

end LogKummerUpperSemiData

/-! ## Non-vacuity and strict one-sidedness -/

/-- The upper-ray family on ℤ, mapping m to the set of integers z with z <= m: the
standard model of a strictly growing upper-semi family, matching the upper-bound
direction of the label `(CnfInd3)`. -/
def upperRayPossibleImage (m : ℤ) : PossibleImage ℤ where
  carrier := {z | z ≤ m}

theorem upperRayPossibleImage_monotone : Monotone upperRayPossibleImage := by
  intro m m' hmm' z hz
  have hz' : z ≤ m := by simpa [upperRayPossibleImage] using hz
  exact ⟨z, by simpa [upperRayPossibleImage] using le_trans hz' hmm', le_rfl⟩

/-- The upper-semi comparison is strictly one-sided: the dominance is not
symmetric, so no reverse (lower bound) comparison follows from it. -/
theorem upperRayPossibleImage_strict {m m' : ℤ} (h : m < m') :
    upperRayPossibleImage m < upperRayPossibleImage m' := by
  refine ⟨upperRayPossibleImage_monotone h.le, ?_⟩
  intro hback
  have hmem : m' ∈ upperRayPossibleImage m' := by
    simp [upperRayPossibleImage]
  obtain ⟨w, hw, hm'w⟩ := hback m' hmem
  have hw' : w ≤ m := by simpa [upperRayPossibleImage] using hw
  exact (not_le_of_gt h) (le_trans hm'w hw')

/-- The total possible-image data: every image is the full carrier.  This witness
shows that the clause carrier of the reduction is not empty. -/
def totalUpperSemiData (β : Type v) [Preorder β] : LogKummerUpperSemiData β where
  kummerImage := fun _ => ⟨Set.univ⟩
  iterateImage := fun _ _ => ⟨Set.univ⟩
  coricModule := ⟨Set.univ⟩
  kummer_subset_coric := fun _ => Set.subset_univ _
  iterate_subset_coric := fun _ _ => Set.subset_univ _
  archBall := fun _ => ⟨Set.univ⟩
  unitImage := fun _ => ⟨Set.univ⟩
  piBallImage := fun _ => ⟨Set.univ⟩
  unit_in_ball := fun _ => Set.subset_univ _
  piBall_in_ball := fun _ => Set.subset_univ _
  logIterate := fun _ _ => id
  iterateDefinedUnits := fun _ _ => ⟨Set.univ⟩
  arch_surjects := fun _ _ z _ => ⟨z, by simp, rfl⟩

theorem logKummerUpperSemiData_nonempty (β : Type v) [Preorder β] :
    Nonempty (LogKummerUpperSemiData β) :=
  ⟨totalUpperSemiData β⟩

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Status record for the `(Ind3)` upper-semi reduction. -/
def ind3UpperSemiReduction : Obligation :=
  { id := "IUT-III.Ind3.upper-semi-reduction"
    source := "IUT III, Theorem 3.11, (ii), (Ind3); Proposition 3.5, (ii), (a), (b)"
    status := VerificationStatus.conditional
    note :=
      "Reduction form proved: the one-sided dominance preorder on possible " ++
      "images, its equivalence with the UpperSemiCorrespondence kernel, the " ++
      "tensor/place assembly, the nonarchimedean containment and the " ++
      "archimedean surjective-cover mechanisms, and the VerticalLogKummer " ++
      "iterate bridge. The source clauses for the actual tensor packets are " ++
      "carried as explicit fields; the unconditional source instance remains " ++
      "open, with its card recorded in the reduction report."
    dependsOn := [ "IUT-II.vertical-log-kummer-correspondence",
      "IUT-III.generic-quotient-transport",
      "IUT-III.Ind3.upper-semi-kernel" ] }

end LeanFormal.IUT.Audit

end