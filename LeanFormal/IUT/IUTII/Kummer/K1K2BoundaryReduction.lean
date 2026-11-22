import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Construction
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# K1/K2 boundary reduction pass

This module reduces the two source-facing boundaries frozen in
`IUTIII/Theorem311/SourceK1K2Construction.lean` (`K1VerticalBoundary` and
`K2FrobenioidBoundary`, obligations `IUT-III.K1.vertical-log-kummer-boundary`
and `IUT-III.K2.frobenioid-mod-realification-boundary`) field by field, against
the already established material: the packet realization's Ind3 upper-semi law
(`SourcePacketRealization.image_ind3`), the ordered vertical contract
(`VerticalLogKummerCorrespondence`), the evaluation bridge of the source
realization, and canonical structure completions.

## K1

Every inhabitant of `K1VerticalBoundary P Q` forces, and is conversely built
from, the three object-level conditions on `(P, Q)` named
`nonarchimedeanImageInclusion`, `ind3ImageWellDefined`, and
`archimedeanTargetLift` (the "image cards").  The remaining fields are
answered as follows:

* `vertical`, `vertical_monotone`: constructed from the packet's Ind3 images
  (`verticalCorrespondenceOfPacket`);
* `nonarchimedeanImage`, `archimedeanImage`: explicit canonical extensions of
  the profile data, built only from the cards;
* `labelledKummer`, `labelled_label`: the kummer slot is not tied to `(P, Q)`
  by any law of the frozen record; it is parameterized in the construction and
  the identity labelled iso inhabits it.  The arithmetic identification of the
  Kummer layers is not part of this interface.

The exact characterization is `k1VerticalBoundary_nonempty_iff`.

## K2

* `upperSemi`, `upperSemi_eq_k1`: the K1 vertical correspondence itself;
* `comparison` and its four alignment equations: constructed from
  `R.evaluation.evaluation` once the two evaluation components
  `localComp`/`globalComp` are pointwise identity, which is exactly the
  necessary and sufficient extra content (`k2FrobenioidBoundary_nonempty_iff`);
* `mod_realification`, `MOD_realification`: derived from `mod_degree` /
  `MOD_degree` and the Frobenioid law `degree_realification`; they are not
  independent source fields;
* `localFrobenioid`, `globalFrobenioid`: a `SourceProposition37Frobenioid`
  record has a canonical completion from its degree monoid hom
  (`sourceProposition37FrobenioidOfDegree`); a faithful assembly keeps the
  supplied records so that any source transport content is preserved;
* `modMap`, `MODMap`, `mod_degree`, `MOD_degree`, `mod_transport`,
  `MOD_transport`: kept as named premise cards for the faithful assembly
  `k2FromFrobenioidCards`; the gate-only witness
  `k2FromTrivialSourceData` records that they are not obstructions to
  inhabitation at this interface.

No field of the two records is asserted to be produced by the arithmetic
constructions of the paper: the cards remain source-facing, and the identity
completions above only witness that the frozen interfaces are satisfiable
once the cards hold.  Nothing in this file modifies the frozen records.

## Source locations (original text under `papers/motizuki_corpus/text`)

* K1 vertical log-Kummer data: IUT III, Proposition 3.5 ("Kummer Theory and
  Upper Semi-compatibility for Vertically Coric Local LGP-Monoids"), (i) (the
  Kummer isomorphisms of monoids of labeled data), (ii), (a) (nonarchimedean
  primes: the module "contains the images" of the Galois-invariant submodules
  of the groups of units), and (ii), (b) (archimedean primes: the closed unit
  ball contains the images of the units and of the closed balls of radius pi,
  and "surjects" onto the units of the domain); Theorem 3.11, (ii), (Ind3)
  ("a sense that involves certain natural inclusions at vQ in Vnon_Q and
  certain natural surjections at vQ in Varc_Q"); the discussion of (Ind3) in
  section 1 of IUT III; IUT II, Definition 4.9, (i) (times- and times-mu-
  Kummer structures).
* K2 Frobenioid / MOD/mod / degree / realification data: IUT III, Proposition
  3.7, (i), (ii) (the Frobenioids (F-MOD)_alpha and (F-mod)_alpha, their
  natural isomorphisms, and the realifications (F-R-MOD)_alpha); Proposition
  3.10, (i); Theorem 3.11, (i), (c) ("natural isomorphisms between the
  associated global non-realified/realified Frobenioids", "whose associated
  `global degrees` may be computed by means of the log-volumes").
* "Possible images": IUT III, section 1 (the union of the collection of
  possible images of the Theta-pilot object in the multiradial representation,
  subject to the indeterminacies (Ind1), (Ind2), (Ind3); cf. Step (xi) of the
  proof of Corollary 3.12).
* Evaluation bridge: IUT II, Corollary 4.10, (ii) (the evaluation isomorphism
  of F-prime-strips); Corollary 4.6, (iii), (iv), (v).

Terminology note: the records reduced here are the frozen abstractions of
`SourceK1K2Construction.lean`; the cards below render the object-level content
that the original attaches to the constructions quoted above.  Statements
about the frozen records (including the two `*_nonempty_iff` theorems and the
K2 evaluation identity equations) are reduced forms; they do not replace the
original propositions, which remain unproved here.  See
`logs/coordination/k1k2-boundary-reduction-20261016.md`, section 8.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w ux uy

namespace K1K2BoundaryReduction

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. K1: the three image-level cards -/

/-- Card N1 (nonarchimedean inclusion of possible images).

Object: the source LGP procession `P` and packet realization `Q`, through
their `ind3` transport and `possibleImage` family.  Quantifiers:
`∀ m c`, `Q.possibleImage c ⊆ Q.possibleImage (P.ind3 m c)`.

Every inhabitant of `K1VerticalBoundary P Q` forces this condition: apply
`nonarchimedean_inclusion` at `S = Q.possibleImage c` and rewrite with
`nonarchimedean_profile`.  It is not derivable from the packet laws alone:
`SourcePacketRealization.image_ind3` only produces an upper bound for each
`z ∈ Q.possibleImage c`, never membership of `z` itself.  A concrete failure
of the packet-only theory is `possibleImage c = {0}` for `c < 2` and `{1}`
otherwise with `ind3 n c = c + n`, which satisfies the packet laws while
`Q.possibleImage 1 ⊄ Q.possibleImage (P.ind3 1 1)`.

Consumers: the K1 nonarchimedean fields, and through them the APT/Corollary
3.12 Step (xi-c) and Ind3 reads of the vertical log-Kummer directions.

Original: IUT III, Proposition 3.5, (ii), (a), and Theorem 3.11, (ii),
(Ind3) ("certain natural inclusions at vQ in Vnon_Q").  This card renders
those inclusions on the `possibleImage` family; the module-theoretic content
(log-shells, tensor packets, Galois invariants) is not formalized here. -/
def nonarchimedeanImageInclusion (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) : Prop :=
  ∀ (m : Nat) (c : Choice), Q.possibleImage c ⊆ Q.possibleImage (P.ind3 m c)

/-- Card N2 (well-definedness of the Ind3 target image).

Object: `(P, Q)`.  Quantifiers: `∀ m c c'`, from
`Q.possibleImage c = Q.possibleImage c'` conclude
`Q.possibleImage (P.ind3 m c) = Q.possibleImage (P.ind3 m c')`.

Every inhabitant of `K1VerticalBoundary P Q` forces this: the profile field
`nonarchimedean_profile` says `nonarchimedeanImage m (Q.possibleImage c)` is
`Q.possibleImage (P.ind3 m c)`, and the left-hand side is the same function
value for `c` and `c'` once the images agree.  The packet laws alone do not
give it: with two choices `(false, n)` and `(true, n)` sharing
`possibleImage (b, n) = {x : Real | x ≤ n}` and
`ind3 m (b, n) = (b, n + (if b then m else 2 * m))` all packet laws hold while
the `m = 1` target images at `n = 0` differ.

Consumers: the two profile fields of the K1 boundary; without N2 no function
`nonarchimedeanImage`/`archimedeanImage` in `Nat → Set Real → Set Real` can
satisfy them, so N2 is not bookkeeping but a consistency condition on `Q`.

Original: the log-Kummer correspondences of IUT III, Theorem 3.11, (ii) are
well defined only up to the indeterminacies (Ind1), (Ind2), (Ind3) (cf. the
discussion of (Ind3) in section 1 of IUT III).  This card is a reduced form:
it renders "the Ind3 target image is well defined" as a consistency condition
on `(P, Q)`; it is not itself a statement of the original. -/
def ind3ImageWellDefined (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) : Prop :=
  ∀ (m : Nat) (c c' : Choice), Q.possibleImage c = Q.possibleImage c' →
    Q.possibleImage (P.ind3 m c) = Q.possibleImage (P.ind3 m c')

/-- Card A1 (archimedean target-to-source lift).

Object: `(P, Q)`.  Quantifiers: `∀ m c z`, membership
`z ∈ Q.possibleImage (P.ind3 m c)` yields `y ∈ Q.possibleImage c` with
`z ≤ y`.

Every inhabitant of `K1VerticalBoundary P Q` forces this: rewrite the
membership through `archimedean_profile` into
`archimedeanImage m (Q.possibleImage c)` and apply `archimedean_surjection`.
It is not derivable from the packet laws: in the down-closed model
`possibleImage (b, n) = {x : Real | x ≤ n}`, `ind3 m (b, n) = (b, n + m)`,
`image_ind3` holds while the lift fails at `z = n + 1` for `m = 1`.

Consumers: the K1 archimedean field and the `archimedean_target_lift` reads
of the Step (xi-c) direction.

Original: IUT III, Proposition 3.5, (ii), (b) (the closed unit ball contains
the images of the units and of the closed balls of radius pi, and contains a
subset that "surjects" onto the units of the domain), and Theorem 3.11, (ii),
(Ind3) ("certain natural surjections at vQ in Varc_Q").  The real inequality
`z ≤ y` renders the direction of that surjection; a reduced form. -/
def archimedeanTargetLift (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) : Prop :=
  ∀ (m : Nat) (c : Choice) (z : Real), z ∈ Q.possibleImage (P.ind3 m c) →
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y

/-! ## 2. K1: constructions from the cards -/

/-- The canonical labelled Kummer isomorphism on an index type: the identity
bijection with the constant label.  The frozen records impose only bijectivity
and the round-trip label law on the kummer slot, so this inhabits it; it
carries no arithmetic identification of log-shells, which the interfaces do
not express.

Original: IUT II, Definition 4.9, (i) (a times-mu-Kummer structure is an
Ism-orbit of isomorphisms of unit modules); IUT III, Proposition 3.5, (i). -/
def identityLabelledKummerIso (A : Type u) : LabelledKummerIso A A where
  map := id
  inverse := id
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl
  label := fun _ => 0
  label_map := fun _ => rfl

/-- The vertical correspondence carried by the packet's Ind3 images, based at
`P.base`.  The upper-semi law is the packet's `image_ind3` transported along
`ind3_add`.

Original: the upper semi-compatibility of IUT III, Proposition 3.5, (ii) and
Theorem 3.11, (ii), (Ind3), specialized to the vertical line; the original
indexes the log-links by m in Z, while the frozen packet `ind3` is
`Nat`-indexed (reduced form). -/
def verticalCorrespondenceOfPacket (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) : UpperSemiCorrespondence Nat Real where
  image m := Q.possibleImage (P.ind3 m P.base)
  upper := by
    intro x y hxy z hz
    have hsplit : P.ind3 y P.base = P.ind3 (y - x) (P.ind3 x P.base) := by
      rw [← P.ind3_add x (y - x) P.base, Nat.add_sub_cancel' hxy]
    obtain ⟨w, hw, hzw⟩ := Q.image_ind3 (y - x) (P.ind3 x P.base) z hz
    exact ⟨w, hsplit.symm ▸ hw, hzw⟩

@[simp] theorem verticalCorrespondenceOfPacket_image
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (m : Nat) :
    (verticalCorrespondenceOfPacket P Q).image m =
      Q.possibleImage (P.ind3 m P.base) := rfl

open Classical in
/-- The canonical nonarchimedean set map: on a possible image it is the Ind3
target image, on all other sets it is the identity.  The profile law for this
function is exactly card N2; the inclusion law is card N1. -/
noncomputable def nonarchimedeanImageOfPacket
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (m : Nat) (S : Set Real) : Set Real :=
  if h : ∃ c : Choice, Q.possibleImage c = S then
    Q.possibleImage (P.ind3 m (Classical.choose h))
  else S

open Classical in
/-- The canonical archimedean set map: on a possible image it is the Ind3
target image, on all other sets it is empty.  The profile law is card N2 and
the surjection law is card A1. -/
noncomputable def archimedeanImageOfPacket
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (m : Nat) (S : Set Real) : Set Real :=
  if h : ∃ c : Choice, Q.possibleImage c = S then
    Q.possibleImage (P.ind3 m (Classical.choose h))
  else ∅

theorem nonarchimedeanImageOfPacket_inclusion
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hInc : nonarchimedeanImageInclusion P Q)
    (m : Nat) (z : Real) (S : Set Real) (hz : z ∈ S) :
    z ∈ nonarchimedeanImageOfPacket P Q m S := by
  classical
  unfold nonarchimedeanImageOfPacket
  by_cases h : ∃ c : Choice, Q.possibleImage c = S
  · rw [dif_pos h]
    exact hInc m h.choose (by rwa [Classical.choose_spec h])
  · rw [dif_neg h]
    exact hz

theorem nonarchimedeanImageOfPacket_profile
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hWD : ind3ImageWellDefined P Q)
    (m : Nat) (c : Choice) :
    nonarchimedeanImageOfPacket P Q m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) := by
  classical
  unfold nonarchimedeanImageOfPacket
  have h : ∃ c' : Choice, Q.possibleImage c' = Q.possibleImage c := ⟨c, rfl⟩
  rw [dif_pos h]
  exact hWD m h.choose c (Classical.choose_spec h)

theorem archimedeanImageOfPacket_surjection
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hLift : archimedeanTargetLift P Q)
    (m : Nat) (z : Real) (S : Set Real)
    (hz : z ∈ archimedeanImageOfPacket P Q m S) :
    ∃ y, y ∈ S ∧ z ≤ y := by
  classical
  unfold archimedeanImageOfPacket at hz
  by_cases h : ∃ c : Choice, Q.possibleImage c = S
  · rw [dif_pos h] at hz
    obtain ⟨y, hy, hzy⟩ := hLift m h.choose z hz
    exact ⟨y, Classical.choose_spec h ▸ hy, hzy⟩
  · rw [dif_neg h] at hz
    exact False.elim hz

theorem archimedeanImageOfPacket_profile
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hWD : ind3ImageWellDefined P Q)
    (m : Nat) (c : Choice) :
    archimedeanImageOfPacket P Q m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) := by
  classical
  unfold archimedeanImageOfPacket
  have h : ∃ c' : Choice, Q.possibleImage c' = Q.possibleImage c := ⟨c, rfl⟩
  rw [dif_pos h]
  exact hWD m h.choose c (Classical.choose_spec h)

/-! ## 3. K1: necessity of the cards -/

theorem k1Boundary_possibleImage_subset
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (K : K1VerticalBoundary P Q) : nonarchimedeanImageInclusion P Q :=
  fun m c z hz => by
    have hmem : z ∈ K.nonarchimedeanImage m (Q.possibleImage c) :=
      K.nonarchimedean_inclusion m z _ hz
    rwa [K.nonarchimedean_profile m c] at hmem

theorem k1Boundary_possibleImage_congr
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (K : K1VerticalBoundary P Q) : ind3ImageWellDefined P Q :=
  fun m c c' h => by
    show Q.possibleImage (P.ind3 m c) = Q.possibleImage (P.ind3 m c')
    rw [← K.nonarchimedean_profile m c, ← K.nonarchimedean_profile m c']
    exact congrArg (K.nonarchimedeanImage m) h

theorem k1Boundary_possibleImage_lift
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (K : K1VerticalBoundary P Q) : archimedeanTargetLift P Q :=
  fun m c z hz => by
    apply K.archimedean_surjection m z (Q.possibleImage c)
    rwa [K.archimedean_profile m c]

theorem sourceVertical_possibleImage_subset
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (V : SourceVerticalRealization P Q) : nonarchimedeanImageInclusion P Q :=
  fun m c z hz => by
    have hmem : z ∈ V.nonarchimedeanImage m (Q.possibleImage c) :=
      V.nonarchimedean_inclusion m z _ hz
    rwa [V.nonarchimedean_profile m c] at hmem

theorem sourceVertical_possibleImage_congr
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (V : SourceVerticalRealization P Q) : ind3ImageWellDefined P Q :=
  fun m c c' h => by
    show Q.possibleImage (P.ind3 m c) = Q.possibleImage (P.ind3 m c')
    rw [← V.nonarchimedean_profile m c, ← V.nonarchimedean_profile m c']
    exact congrArg (V.nonarchimedeanImage m) h

theorem sourceVertical_possibleImage_lift
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (V : SourceVerticalRealization P Q) : archimedeanTargetLift P Q :=
  fun m c z hz => by
    apply V.archimedean_surjection m z (Q.possibleImage c)
    rwa [V.archimedean_profile m c]

/-! ## 4. K1: assembly and characterization -/

/-- Assembly of the K1 boundary from the three image cards plus the labelled
Kummer data.  The kummer slot is passed through unchanged: the frozen record
imposes no law relating it to `(P, Q)`. -/
def k1FromImageCards
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hInc : nonarchimedeanImageInclusion P Q)
    (hWD : ind3ImageWellDefined P Q)
    (hLift : archimedeanTargetLift P Q)
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    K1VerticalBoundary P Q where
  vertical := verticalCorrespondenceOfPacket P Q
  vertical_monotone := fun m n h z hz =>
    (verticalCorrespondenceOfPacket P Q).upper h z hz
  nonarchimedeanImage := nonarchimedeanImageOfPacket P Q
  archimedeanImage := archimedeanImageOfPacket P Q
  nonarchimedean_inclusion := fun m z S hz =>
    nonarchimedeanImageOfPacket_inclusion P Q hInc m z S hz
  archimedean_surjection := fun m z S hz =>
    archimedeanImageOfPacket_surjection P Q hLift m z S hz
  nonarchimedean_profile := fun m c =>
    nonarchimedeanImageOfPacket_profile P Q hWD m c
  archimedean_profile := fun m c =>
    archimedeanImageOfPacket_profile P Q hWD m c
  labelledKummer := κ
  labelled_label := fun c a => (κ c).label_map a

/-- Exact characterization of the K1 gate: `K1VerticalBoundary P Q` is
inhabited if and only if the three object-level cards hold.  The forward
direction is necessity for every inhabitant (including any source-supplied
realization); the backward direction uses the identity labelled Kummer slot,
which is the only content of the kummer fields at this interface.

Reduced form: this characterizes inhabitation of the frozen K1 record, not
the original statement of IUT III, Proposition 3.5; the three cards it names
remain unproved, so the original content remains a source gap. -/
theorem k1VerticalBoundary_nonempty_iff
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P) :
    Nonempty (K1VerticalBoundary P Q) ↔
      nonarchimedeanImageInclusion P Q ∧ ind3ImageWellDefined P Q ∧
        archimedeanTargetLift P Q := by
  constructor
  · rintro ⟨K⟩
    exact ⟨k1Boundary_possibleImage_subset P Q K,
      k1Boundary_possibleImage_congr P Q K,
      k1Boundary_possibleImage_lift P Q K⟩
  · rintro ⟨hInc, hWD, hLift⟩
    exact ⟨k1FromImageCards P Q hInc hWD hLift
      (fun _ => identityLabelledKummerIso Choice)⟩

/-! ## 5. K2: the Proposition 3.7 record is a degree hom -/

/-- Canonical completion of the frozen Proposition 3.7 Frobenioid record from
a degree monoid hom: `realification` is the underlying additive value of
`degree`, the unit is `1`, every element is effective, and `transport` is the
identity.  Every law of the record holds by construction.  Any supplied
record contains such a degree hom (`F.degree`), so the substantive content of
the record at this interface is the degree; a faithful assembly still passes
the supplied record unchanged so that any transport content is preserved.

Original: IUT III, Proposition 3.7, (i), (ii) (the packet-theoretic
Frobenioids (F-MOD)_alpha, (F-mod)_alpha and their realifications), and
Theorem 3.11, (i), (c).  The frozen `SourceProposition37Frobenioid` is a
degree-hom abstraction of that Frobenioid structure; this completion is a
reduced form. -/
def sourceProposition37FrobenioidOfDegree {X : Type ux} [CommMonoid X]
    (d : X →* Multiplicative Real) : SourceProposition37Frobenioid X where
  degree := d
  realification := fun x => Multiplicative.toAdd (d x)
  realification_mul := fun x y => by
    rw [map_mul]
    rfl
  degree_realification := fun _ => rfl
  unit := 1
  unit_realification := by
    rw [map_one]
    rfl
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := fun x => x
  transport_degree := fun _ => rfl

/-! ## 6. K2: the comparison package from the evaluation bridge -/

/-- Construction of the frozen Proposition 3.10 comparison package from the
evaluation system of a source realization, given that the two evaluation
components `localComp` and `globalComp` are pointwise identity.  The labelled
data of the comparison package is not tied to the evaluation by the frozen
record and is filled with the identity (labelled map, inverse, zero labels);
the lower/upper maps must equal `localComp`/`globalComp`, which is why the two
identity equations are exactly the extra content.

Original: IUT II, Corollary 4.10, (ii) (the evaluation isomorphism of
F-prime-strips); IUT III, Proposition 3.10, (i), and Theorem 3.11, (ii).
The frozen `SourceProposition310Comparison` is an abstraction; this
construction is a reduced form. -/
def sourceProposition310ComparisonOfEvaluation {A : Type u}
    (E : EvaluationSystem A A)
    (hLocal : ∀ a, E.localComp a = a)
    (hGlobal : ∀ a, E.globalComp a = a) :
    SourceProposition310Comparison A A where
  localMap := E.localMap
  globalMap := E.globalMap
  localEqGlobal := E.localEqGlobal
  lower := E.localComp
  upper := E.globalComp
  square := fun a => by
    rw [hGlobal]
    exact (E.localNaturality a).symm
  labelledMap := id
  labelledInverse := id
  labelledLeft := fun _ => rfl
  labelledRight := fun _ => rfl
  label := fun _ => 0
  label_target := fun _ => 0
  label_compat := fun _ => rfl
  lower_natural := hLocal
  upper_natural := hGlobal

/-! ## 7. K2: necessity of the evaluation identity equations -/

/-- Necessity direction for the first K2 evaluation identity (reduced form,
about the frozen `K2FrobenioidBoundary` record): the `comparison_lower`
alignment and the `lower_natural` law force `localComp` to be pointwise
identity in every inhabitant. -/
theorem k2Boundary_localComp_eq_id
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (B : K2FrobenioidBoundary R K X Y) :
    ∀ a, R.evaluation.evaluation.localComp a = a :=
  fun a => (congrFun B.comparison_lower a).symm.trans
    (B.comparison.lower_natural a)

/-- Necessity direction for the second K2 evaluation identity (reduced form,
about the frozen `K2FrobenioidBoundary` record): the `comparison_upper`
alignment and the `upper_natural` law force `globalComp` to be pointwise
identity in every inhabitant. -/
theorem k2Boundary_globalComp_eq_id
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (B : K2FrobenioidBoundary R K X Y) :
    ∀ b, R.evaluation.evaluation.globalComp b = b :=
  fun b => (congrFun B.comparison_upper b).symm.trans
    (B.comparison.upper_natural b)

/-! ## 8. K2: faithful assembly -/

/-- Assembly of the K2 boundary from supplied Frobenioid records, the two
mod/MOD maps with their degree and transport equations, and the two
evaluation identity equations.  The realification equations and the comparison
package are derived, not assumed; the supplied records are passed unchanged.

Original: IUT III, Theorem 3.11, (i), (c) (the natural isomorphisms between
the non-realified and realified MOD/mod Frobenioids, "whose associated `global
degrees` may be computed by means of the log-volumes"; cf. Proposition 3.10,
(i); Proposition 3.7, (i), (ii)).  The eight supply arguments are reduced
forms of the source transport content. -/
def k2FromFrobenioidCards
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (localFrobenioid : SourceProposition37Frobenioid X)
    (globalFrobenioid : SourceProposition37Frobenioid Y)
    (modMap : X → Y) (MODMap : Y → X)
    (mod_degree : ∀ x,
      globalFrobenioid.degree (modMap x) = localFrobenioid.degree x)
    (MOD_degree : ∀ y,
      localFrobenioid.degree (MODMap y) = globalFrobenioid.degree y)
    (mod_transport : ∀ x,
      modMap (localFrobenioid.transport x) =
        globalFrobenioid.transport (modMap x))
    (MOD_transport : ∀ y,
      MODMap (globalFrobenioid.transport y) =
        localFrobenioid.transport (MODMap y))
    (hLocalComp : ∀ a, R.evaluation.evaluation.localComp a = a)
    (hGlobalComp : ∀ b, R.evaluation.evaluation.globalComp b = b) :
    K2FrobenioidBoundary R K X Y where
  localFrobenioid := localFrobenioid
  globalFrobenioid := globalFrobenioid
  modMap := modMap
  MODMap := MODMap
  mod_degree := mod_degree
  MOD_degree := MOD_degree
  mod_realification := fun x =>
    ((globalFrobenioid.degree_realification (modMap x)).symm).trans
      ((congrArg (fun r : Multiplicative Real => (r : Real))
        (mod_degree x)).trans
        (localFrobenioid.degree_realification x))
  MOD_realification := fun y =>
    ((localFrobenioid.degree_realification (MODMap y)).symm).trans
      ((congrArg (fun r : Multiplicative Real => (r : Real))
        (MOD_degree y)).trans
        (globalFrobenioid.degree_realification y))
  mod_transport := mod_transport
  MOD_transport := MOD_transport
  comparison := sourceProposition310ComparisonOfEvaluation
    R.evaluation.evaluation hLocalComp hGlobalComp
  comparison_local := by dsimp only [sourceProposition310ComparisonOfEvaluation]
  comparison_global := by dsimp only [sourceProposition310ComparisonOfEvaluation]
  comparison_lower := by dsimp only [sourceProposition310ComparisonOfEvaluation]
  comparison_upper := by dsimp only [sourceProposition310ComparisonOfEvaluation]
  upperSemi := K.vertical
  upperSemi_eq_k1 := rfl

/-- The gate witness: with trivial source data (constant-one degrees, constant
maps to `1`, identity transport) the remaining content of the K2 record is
exactly the two evaluation identity equations.  This witness is recorded for
the gate characterization only; it erases all degree and transport content
and is not a source-faithful realization.  It has no original counterpart and
is recorded only for the gate characterization. -/
def k2FromTrivialSourceData
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (hLocalComp : ∀ a, R.evaluation.evaluation.localComp a = a)
    (hGlobalComp : ∀ b, R.evaluation.evaluation.globalComp b = b) :
    K2FrobenioidBoundary R K X Y :=
  k2FromFrobenioidCards R K
    (sourceProposition37FrobenioidOfDegree (1 : X →* Multiplicative Real))
    (sourceProposition37FrobenioidOfDegree (1 : Y →* Multiplicative Real))
    (fun _ => 1) (fun _ => 1)
    (fun _ => by simp [sourceProposition37FrobenioidOfDegree])
    (fun _ => by simp [sourceProposition37FrobenioidOfDegree])
    (fun _ => by simp [sourceProposition37FrobenioidOfDegree])
    (fun _ => by simp [sourceProposition37FrobenioidOfDegree])
    hLocalComp hGlobalComp

/-- Exact characterization of the K2 gate: `K2FrobenioidBoundary R K X Y` is
inhabited if and only if the two evaluation components are pointwise
identity.  The forward direction is necessity for every inhabitant; the
backward direction uses the trivial source data completion.  The
characterization concerns inhabitation at the frozen interface only; a
source-faithful boundary should be assembled with `k2FromFrobenioidCards`.

Reduced form: the evaluation identity equations are a property of the frozen
abstraction (the original counterpart is the evaluation isomorphism of IUT
II, Corollary 4.10, (ii), and the labelled Kummer isomorphisms of IUT III,
Theorem 3.11, (ii)); the original propositions remain unproved here. -/
theorem k2FrobenioidBoundary_nonempty_iff
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y] :
    Nonempty (K2FrobenioidBoundary R K X Y) ↔
      (∀ a, R.evaluation.evaluation.localComp a = a) ∧
        (∀ b, R.evaluation.evaluation.globalComp b = b) := by
  constructor
  · rintro ⟨B⟩
    exact ⟨k2Boundary_localComp_eq_id R K B, k2Boundary_globalComp_eq_id R K B⟩
  · rintro ⟨hLocalComp, hGlobalComp⟩
    exact ⟨k2FromTrivialSourceData R K hLocalComp hGlobalComp⟩

end K1K2BoundaryReduction

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the K1/K2 boundary reduction pass.  It documents the
field-by-field disposition of `K1VerticalBoundary` and `K2FrobenioidBoundary`
against the already proved material, the three K1 image cards, the two K2
evaluation identity equations, and the two gate characterizations.  It does
not assert that the cards hold, nor that the paper's log-shell, Frobenioid,
or MOD/mod constructions have been built. -/
def k1k2BoundaryReductionPass : Obligation :=
  { id := "IUT-III.k1k2-boundary-reduction"
    source := "IUT II, Definition 4.9, (i); Corollaries 4.6, 4.10, (ii); " ++
      "IUT III, Proposition 3.5, (i), (ii); Propositions 3.7, 3.10, (i); " ++
      "Theorem 3.11, (i), (c), (ii), (Ind3)"
    status := VerificationStatus.interface
    note :=
      "K1 reduces exactly to three object-level cards on the packet " ++
        "realization (nonarchimedeanImageInclusion, ind3ImageWellDefined, " ++
        "archimedeanTargetLift); the vertical correspondence, the two site " ++
        "maps, and the labelled Kummer slot are constructed, and the " ++
        "inhabitation characterization k1VerticalBoundary_nonempty_iff is " ++
        "proved. K2 keeps local/global Frobenioid records, mod/MOD maps, " ++
        "their degree and transport equations as named cards; the " ++
        "realification equations derive from the degree equations, the " ++
        "comparison package derives from the evaluation bridge given " ++
        "pointwise identity localComp/globalComp, and the gate " ++
        "characterization k2FrobenioidBoundary_nonempty_iff is proved. " ++
        "NOT proved: any of the five cards; no source construction of " ++
        "log-shells, Frobenioid carriers, or MOD/mod maps; the trivial and " ++
        "identity completions are gate witnesses only and carry no " ++
        "arithmetic content. No frozen record is modified. Source locations " ++
        "and reduced-form labels: see the module docstring and the pass " ++
        "report section 8."
    dependsOn :=
      [ "IUT-III.K1.vertical-log-kummer-boundary",
        "IUT-III.K2.frobenioid-mod-realification-boundary",
        "IUT-II.vertical-log-kummer-correspondence",
        "IUT-III.Ind3.upper-semi-kernel" ] }

end LeanFormal.IUT.Audit
