import LeanFormal.IUT.IUTIII.Theorem311.HullPresentationAlternativeProbe
import LeanFormal.IUT.IUTII.Kummer.K1K2BoundaryReduction
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-!
# Pack A: discharge test of the R1 envelope shape conditions

Probe file (run `hull-presentation-routes-20261016`, agent Noether).  Read-only
with respect to every other file; it adds declarations only and modifies
nothing.

The `hpres` route (`LogShellRayPresentation`) is false in general
(`not_logShellRayPresentation_of_two_singletonImages`).  As its replacement,
`HullPresentationAlternativeProbe` derives the three frozen K1 image cards

* N1 `K1K2BoundaryReduction.nonarchimedeanImageInclusion`,
* N2 `K1K2BoundaryReduction.ind3ImageWellDefined`,
* A1 `K1K2BoundaryReduction.archimedeanTargetLift`

from shape conditions on the packet `Q`.  This file is the discharge test of
those shapes on the source-audited concrete carrier
(`ConcreteFiniteTheorem311`) and at the frozen interface.

## Tri-state table (exact status, nothing mixed)

* N1.  Reduction "down-closed Ind3 targets give N1": *proved* (probe,
  `nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed`).  Shape
  hypothesis: *additional-data*.  It is refuted on the concrete finite model
  (`finiteOutput_target_not_downClosed`), and the card itself fails there
  (`not_finiteOutput_nonarchimedeanImageInclusion`); frozen-level witness
  schema `not_nonarchimedeanImageInclusion_of_lifted_singleton_ne`.
* A1.  Reduction "unbounded images give A1": *proved* (probe,
  `archimedeanTargetLift_of_possibleImage_unbounded`).  Shape hypothesis:
  *additional-data*.  Refuted on the concrete finite model
  (`finiteOutput_not_unbounded`), and the card fails there
  (`not_finiteOutput_archimedeanTargetLift`); frozen-level witness schema
  `not_archimedeanTargetLift_of_lifted_singleton_lt`.
* N2.  Reduction "down-closed + attained max + factor law give N2": *proved*
  (probe, `ind3ImageWellDefined_of_attainedMax_factorization`).  The card
  itself is *proved* on the concrete finite model through the singleton route
  (`finiteOutput_ind3ImageWellDefined`), although that model satisfies none of
  the down-closure hypotheses of the reduction.  In general the card is *not*
  a consequence of the frozen laws: the two-branch image-lift model satisfies
  every law of `ImageLiftLawModel` and fails N2
  (`not_twoBranchModel_ind3ImageWellDefined`).  New frozen-level reductions:
  `ind3ImageWellDefined_of_singletonImages_factorization` and
  `ind3ImageWellDefined_of_downClosedTargets_unbounded`.

## Corrections and sharper findings

* The joint assembly `k1BoundaryOfEnvelopeConditions` of the probe required
  simultaneously that every image be down-closed, be unbounded and attain a
  maximum; unboundedness and the attained maximum contradict each other
  (`not_envelopeConditions_hypotheses`), so that assembly is vacuous.  The
  corrected jointly satisfiable route is
  `k1VerticalBoundaryOfUnboundedDownClosedTargets`: down-closure of the Ind3
  *target* images plus unboundedness of the images suffice for all three
  cards, because they force every Ind3 target image to be `Set.univ`
  (`possibleImage_ind3_eq_univ_of_downClosedTarget_unbounded`); no separate
  hypothesis for N2 is needed.
* The two genuinely usable shape conditions are therefore (i) down-closure of
  the Ind3 target images and (ii) unboundedness of the possible images.  On
  the source-audited concrete finite model both fail (this file proves it), so
  for that model N1 and A1 remain *additional-data*; N2 is nevertheless true
  there.

No claim about the original IUT text is made: every statement below concerns
the frozen interfaces `SourceLGPProcession`, `SourcePacketRealization`,
`K1K2BoundaryReduction` and `ConcreteFiniteTheorem311`.  Reduced forms are
labelled as such.
-/

namespace LeanFormal.IUT

universe u v

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. The corrected joint route: down-closed targets + unbounded images -/

/-- If every Ind3 target image is down-closed and every possible image is
unbounded above, then every Ind3 target image is the whole real line: the
domination law `image_ind3` bounds the target from below by the unbounded
source image, and down-closure fills the interval downward.

This is the corrected replacement for the N2 leg of
`k1BoundaryOfEnvelopeConditions` (whose hypothesis bundle is unsatisfiable);
whenever the two genuinely usable shape conditions of N1 and A1 hold, N2 is
free. -/
theorem possibleImage_ind3_eq_univ_of_downClosedTarget_unbounded
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hclosed : ∀ m c, ∀ ⦃z w : Real⦄,
      w ∈ Q.possibleImage (P.ind3 m c) → z ≤ w →
        z ∈ Q.possibleImage (P.ind3 m c))
    (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y)
    (m : Nat) (c : Choice) :
    Q.possibleImage (P.ind3 m c) = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    obtain ⟨z₀, hz₀, hzz₀⟩ := hunb c z
    obtain ⟨y, hy, hz₀y⟩ := Q.image_ind3 m c z₀ hz₀
    exact hclosed m c hy (le_trans hzz₀ hz₀y)

/-- N2 from the corrected shape conditions: the well-definedness of the Ind3
target image needs no extra hypothesis once the N1 and A1 shapes hold. -/
theorem ind3ImageWellDefined_of_downClosedTargets_unbounded
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hclosed : ∀ m c, ∀ ⦃z w : Real⦄,
      w ∈ Q.possibleImage (P.ind3 m c) → z ≤ w →
        z ∈ Q.possibleImage (P.ind3 m c))
    (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y) :
    K1K2BoundaryReduction.ind3ImageWellDefined P Q := by
  intro m c c' _
  rw [possibleImage_ind3_eq_univ_of_downClosedTarget_unbounded Q hclosed hunb m c,
    possibleImage_ind3_eq_univ_of_downClosedTarget_unbounded Q hclosed hunb m c']

/-- The three K1 image cards from the two jointly satisfiable shape
conditions. -/
theorem k1ImageCards_of_downClosedTargets_unbounded
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hclosed : ∀ m c, ∀ ⦃z w : Real⦄,
      w ∈ Q.possibleImage (P.ind3 m c) → z ≤ w →
        z ∈ Q.possibleImage (P.ind3 m c))
    (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y) :
    K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q ∧
      K1K2BoundaryReduction.ind3ImageWellDefined P Q ∧
      K1K2BoundaryReduction.archimedeanTargetLift P Q :=
  ⟨nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed Q hclosed,
    ind3ImageWellDefined_of_downClosedTargets_unbounded Q hclosed hunb,
    archimedeanTargetLift_of_possibleImage_unbounded Q hunb⟩

/-- Corrected K1 assembly: down-closure of the Ind3 target images and
unboundedness of the images replace the vacuous envelope bundle of the probe
and the false ray presentation.  Through the same frozen consumer
`K1K2BoundaryReduction.k1FromImageCards`.  Reduced form: inhabitation of the
frozen `K1VerticalBoundary` record, not the original Proposition 3.5. -/
def k1VerticalBoundaryOfUnboundedDownClosedTargets
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hclosed : ∀ m c, ∀ ⦃z w : Real⦄,
      w ∈ Q.possibleImage (P.ind3 m c) → z ≤ w →
        z ∈ Q.possibleImage (P.ind3 m c))
    (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y)
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    K1VerticalBoundary P Q :=
  K1K2BoundaryReduction.k1FromImageCards P Q
    (nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed Q hclosed)
    (ind3ImageWellDefined_of_downClosedTargets_unbounded Q hclosed hunb)
    (archimedeanTargetLift_of_possibleImage_unbounded Q hunb)
    κ

/-- Unboundedness contradicts the attainment of a maximum: no set that is
unbounded above has an element above all of its members. -/
theorem not_attainedMax_of_unbounded {S : Set Real}
    (hunb : ∀ x : Real, ∃ y ∈ S, x ≤ y) :
    ¬ ∃ e : Real, e ∈ S ∧ ∀ z ∈ S, z ≤ e := by
  rintro ⟨e, -, htop⟩
  obtain ⟨y, hy, hey⟩ := hunb (e + 1)
  have hye : y ≤ e := htop y hy
  linarith

/-- The hypothesis bundle of the probe's joint assembly
`k1BoundaryOfEnvelopeConditions` is unsatisfiable on every packet: the
unboundedness clause and the attained-maximum clause contradict each other
already at the base choice.  (Down-closure is not even needed for the
contradiction.)  This is the precise vacuity card for that assembly. -/
theorem not_envelopeConditions_hypotheses
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P) :
    ¬ ∃ (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y)
        (e : Choice → Real),
        ∀ c, e c ∈ Q.possibleImage c ∧ ∀ z ∈ Q.possibleImage c, z ≤ e c := by
  rintro ⟨hunb, e, hatt⟩
  have h := not_attainedMax_of_unbounded (S := Q.possibleImage P.base)
    (hunb := fun x => hunb P.base x)
  exact h ⟨e P.base, (hatt P.base).1, fun z hz => (hatt P.base).2 z hz⟩

/-! ## 2. The source-audited concrete finite model

The concrete model of `ConcreteFiniteTheorem311` (the proved Q(i)-at-5
C-stage carrier) has singleton possible images
`possibleImage c = {normalizedLogVolume l c}` and the shift `ind3Lift` with
`normalizedLogVolume l (ind3Lift m c) = normalizedLogVolume l c + m`
(proved in `SourceK1K2CardReduction`).  No `SourceLGPProcession` instance
over this carrier exists in the tree (the audit note of
`SourceFiniteOutputLawBundleVerticalWiring` records `procession` as open
source data), so the three frozen cards are mirrored below with
`ProcessionChoice.ind3Lift` in the role of `P.ind3`; the formulas are literal
transcriptions. -/

section ConcreteModelTest

open ConcreteFiniteTheorem311

/-- N1 card formula on the concrete finite model. -/
def finiteOutputNonarchimedeanImageInclusion (l : PrimeGeFive)
    (F : FiniteOutput l) : Prop :=
  ∀ (m : Nat) (c : ProcessionChoice l),
    F.possibleImage c ⊆ F.possibleImage (ProcessionChoice.ind3Lift m c)

/-- A1 card formula on the concrete finite model. -/
def finiteOutputArchimedeanTargetLift (l : PrimeGeFive)
    (F : FiniteOutput l) : Prop :=
  ∀ (m : Nat) (c : ProcessionChoice l) (z : Real),
    z ∈ F.possibleImage (ProcessionChoice.ind3Lift m c) →
      ∃ y, y ∈ F.possibleImage c ∧ z ≤ y

/-- N2 card formula on the concrete finite model. -/
def finiteOutputInd3ImageWellDefined (l : PrimeGeFive)
    (F : FiniteOutput l) : Prop :=
  ∀ (m : Nat) (c c' : ProcessionChoice l),
    F.possibleImage c = F.possibleImage c' →
      F.possibleImage (ProcessionChoice.ind3Lift m c) =
        F.possibleImage (ProcessionChoice.ind3Lift m c')

/-- The possible images of the concrete finite model are singletons. -/
theorem finiteOutput_possibleImage_eq_singleton (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (finiteOutput l).possibleImage c = {normalizedLogVolume l c} := rfl

/-- `ind3Lift` by one strictly increases the normalized log-volume. -/
theorem finiteOutput_normalizedLogVolume_lt_ind3Lift_one (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    normalizedLogVolume l c <
      normalizedLogVolume l (ProcessionChoice.ind3Lift 1 c) := by
  rw [normalizedLogVolume_ind3Lift_add]
  exact lt_add_of_pos_right _ (by norm_num)

/-- The Ind3 target images of the concrete finite model are not down-closed:
`{theta + 1}` contains `theta + 1` but not the strictly smaller `theta`. -/
theorem finiteOutput_target_not_downClosed (l : PrimeGeFive) :
    ¬ ∀ (m : Nat) (c : ProcessionChoice l), ∀ ⦃z w : Real⦄,
      w ∈ (finiteOutput l).possibleImage (ProcessionChoice.ind3Lift m c) →
        z ≤ w →
          z ∈ (finiteOutput l).possibleImage (ProcessionChoice.ind3Lift m c) := by
  intro hclosed
  have hmem : normalizedLogVolume l (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) ∈
      (finiteOutput l).possibleImage (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) := by
    rw [finiteOutput_possibleImage_eq_singleton]
    exact Set.mem_singleton _
  have hle : normalizedLogVolume l ProcessionChoice.base ≤
      normalizedLogVolume l (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) := by
    rw [normalizedLogVolume_ind3Lift_add]
    linarith
  have hz := hclosed 1 ProcessionChoice.base hmem hle
  rw [finiteOutput_possibleImage_eq_singleton] at hz
  rw [Set.mem_singleton_iff] at hz
  exact absurd hz (ne_of_lt
    (finiteOutput_normalizedLogVolume_lt_ind3Lift_one l ProcessionChoice.base))

/-- No possible image of the concrete finite model is down-closed. -/
theorem finiteOutput_image_not_downClosed (l : PrimeGeFive) :
    ¬ ∀ (c : ProcessionChoice l), ∀ ⦃z w : Real⦄,
      w ∈ (finiteOutput l).possibleImage c → z ≤ w →
        z ∈ (finiteOutput l).possibleImage c := by
  intro hclosed
  have hmem : normalizedLogVolume l ProcessionChoice.base ∈
      (finiteOutput l).possibleImage ProcessionChoice.base := by
    rw [finiteOutput_possibleImage_eq_singleton]
    exact Set.mem_singleton _
  have hzle : normalizedLogVolume l ProcessionChoice.base - 1 ≤
      normalizedLogVolume l ProcessionChoice.base := by linarith
  have hz := hclosed ProcessionChoice.base hmem hzle
  rw [finiteOutput_possibleImage_eq_singleton] at hz
  rw [Set.mem_singleton_iff] at hz
  linarith

/-- The images of the concrete finite model are bounded above (they are
singletons): the A1 shape hypothesis fails. -/
theorem finiteOutput_not_unbounded (l : PrimeGeFive) :
    ¬ ∀ (c : ProcessionChoice l) (x : Real),
      ∃ y ∈ (finiteOutput l).possibleImage c, x ≤ y := by
  intro hunb
  obtain ⟨y, hy, hxy⟩ := hunb ProcessionChoice.base
    (normalizedLogVolume l ProcessionChoice.base + 1)
  rw [finiteOutput_possibleImage_eq_singleton] at hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  linarith

/-- The N1 card fails on the source-audited concrete finite model: with
`m = 1` and `c = base`, the member `normalizedLogVolume l base` of the source
image is not a member of the target image
`{normalizedLogVolume l base + 1}`.  Hence N1 is not a consequence of the
packet laws. -/
theorem not_finiteOutput_nonarchimedeanImageInclusion (l : PrimeGeFive) :
    ¬ finiteOutputNonarchimedeanImageInclusion l (finiteOutput l) := by
  intro h
  have hmem : normalizedLogVolume l ProcessionChoice.base ∈
      (finiteOutput l).possibleImage ProcessionChoice.base := by
    rw [finiteOutput_possibleImage_eq_singleton]
    exact Set.mem_singleton _
  have hmem' := h 1 ProcessionChoice.base hmem
  rw [finiteOutput_possibleImage_eq_singleton] at hmem'
  rw [Set.mem_singleton_iff] at hmem'
  exact absurd hmem' (ne_of_lt
    (finiteOutput_normalizedLogVolume_lt_ind3Lift_one l ProcessionChoice.base))

/-- The A1 card fails on the source-audited concrete finite model: the lift
value `normalizedLogVolume l base + 1` is in the target image but dominates
the only member of the source image. -/
theorem not_finiteOutput_archimedeanTargetLift (l : PrimeGeFive) :
    ¬ finiteOutputArchimedeanTargetLift l (finiteOutput l) := by
  intro h
  have hmem : normalizedLogVolume l (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) ∈
      (finiteOutput l).possibleImage (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) := by
    rw [finiteOutput_possibleImage_eq_singleton]
    exact Set.mem_singleton _
  obtain ⟨y, hy, hzy⟩ := h 1 ProcessionChoice.base
    (normalizedLogVolume l (ProcessionChoice.ind3Lift 1 ProcessionChoice.base)) hmem
  rw [finiteOutput_possibleImage_eq_singleton] at hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact absurd hzy (not_le_of_gt
    (finiteOutput_normalizedLogVolume_lt_ind3Lift_one l ProcessionChoice.base))

/-- The N2 card *holds* on the source-audited concrete finite model: the
singleton image determines the normalized log-volume, and `ind3Lift` is the
additive shift, so equal source images have equal target images.  This is the
instance of the singleton route
`ind3ImageWellDefined_of_singletonImages_factorization` with
`v = normalizedLogVolume l` and `F m = (· + m)`. -/
theorem finiteOutput_ind3ImageWellDefined (l : PrimeGeFive) :
    finiteOutputInd3ImageWellDefined l (finiteOutput l) := by
  intro m c c' hcc
  have hcc' : ({normalizedLogVolume l c} : Set Real) = {normalizedLogVolume l c'} := by
    rw [← finiteOutput_possibleImage_eq_singleton l c,
      ← finiteOutput_possibleImage_eq_singleton l c']
    exact hcc
  have hv : normalizedLogVolume l c = normalizedLogVolume l c' :=
    Set.singleton_injective.eq_iff.mp hcc'
  rw [finiteOutput_possibleImage_eq_singleton l (ProcessionChoice.ind3Lift m c),
    finiteOutput_possibleImage_eq_singleton l (ProcessionChoice.ind3Lift m c'),
    normalizedLogVolume_ind3Lift_add, normalizedLogVolume_ind3Lift_add, hv]

end ConcreteModelTest

/-! ## 3. Frozen-level separation schemas

The concrete model exhibits the pattern "source image `{v}`, target image
`{v'}`" with `v ≠ v'` (respectively `v < v'`).  The following two schemas
carry that pattern to the frozen interface: any actual `(P, Q)` pair with such
a pattern falsifies N1 (respectively A1). -/

/-- Frozen-level N1 separation: a source image that is a singleton not
preserved by an Ind3 target image falsifies N1. -/
theorem not_nonarchimedeanImageInclusion_of_lifted_singleton_ne
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    {m : Nat} {c : Choice} {v v' : Real}
    (hc : Q.possibleImage c = {v})
    (hc' : Q.possibleImage (P.ind3 m c) = {v'}) (hne : v ≠ v') :
    ¬ K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q := by
  intro hInc
  have hmem : v ∈ Q.possibleImage (P.ind3 m c) :=
    (hInc m c) (by rw [hc]; exact Set.mem_singleton v)
  rw [hc'] at hmem
  exact hne (Set.mem_singleton_iff.mp hmem)

/-- Frozen-level A1 separation: a target image singleton strictly above the
source image singleton falsifies A1. -/
theorem not_archimedeanTargetLift_of_lifted_singleton_lt
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    {m : Nat} {c : Choice} {v v' : Real}
    (hc : Q.possibleImage c = {v})
    (hc' : Q.possibleImage (P.ind3 m c) = {v'}) (hlt : v < v') :
    ¬ K1K2BoundaryReduction.archimedeanTargetLift P Q := by
  intro hLift
  have hmem : v' ∈ Q.possibleImage (P.ind3 m c) := by
    rw [hc']
    exact Set.mem_singleton v'
  obtain ⟨y, hy, hy'⟩ := hLift m c v' hmem
  rw [hc] at hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  linarith

/-! ## 4. N2 at the frozen interface: the singleton route -/

/-- N2 frozen-level singleton route: if every image is the singleton `{v c}`
and the value function factors through `ind3` by a function of `v c` alone,
then the Ind3 target images are well defined.  A sufficient condition of a
different shape from the down-closure/maximum route of the probe; the
concrete finite model is the instance with
`v = normalizedLogVolume l` and `F m = (· + m)`. -/
theorem ind3ImageWellDefined_of_singletonImages_factorization
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (v : Choice → Real) (hsingle : ∀ c, Q.possibleImage c = {v c})
    (hfac : ∀ m, ∃ F : Real → Real, ∀ c, v (P.ind3 m c) = F (v c)) :
    K1K2BoundaryReduction.ind3ImageWellDefined P Q := by
  intro m c c' hcc
  have hv : v c = v c' := by
    have h' : ({v c} : Set Real) = {v c'} := by
      rw [← hsingle c, ← hsingle c']
      exact hcc
    exact Set.singleton_injective.eq_iff.mp h'
  obtain ⟨F, hF⟩ := hfac m
  rw [hsingle (P.ind3 m c), hsingle (P.ind3 m c'), hF c, hF c', hv]

/-! ## 5. N2 is not derivable from the frozen laws: a two-branch witness

`not_twoBranchModel_ind3ImageWellDefined` machine-checks the countermodel
described informally in the N2 docstring of `K1K2BoundaryReduction`.

Fragment scope: `ImageLiftLawModel` lists the laws of `SourceLGPProcession`
and `SourcePacketRealization` whose statements mention `ind1`, `ind2`, `ind3`,
`level`, the possible image or the log-volume, with the label group
specialized to `Int`.  The omitted fields are pure data: the source package
(`hodge`, `base`, `source_index`) appears in no law about the possible image,
and the determinant fields can be completed by `Real.exp` (their log law is
`Real.log_exp` and their monotonicity follows from `Real.exp_le_exp`).  The
witness below therefore shows that N2 is not forced by the image, volume and
indeterminacy part of the frozen laws. -/

/-- The image/volume fragment of the frozen laws, with the label group
specialized to `Int`. -/
structure ImageLiftLawModel where
  Choice : Type
  ind1 : Int → Choice → Choice
  ind2 : Int → Choice → Choice
  ind3 : Nat → Choice → Choice
  level : Choice → Nat
  image : Choice → Set Real
  volume : Choice → Real
  ind1_zero : ∀ c, ind1 0 c = c
  ind1_add : ∀ g h c, ind1 (g + h) c = ind1 h (ind1 g c)
  ind1_inverse : ∀ g c, ind1 (-g) (ind1 g c) = c
  ind2_zero : ∀ c, ind2 0 c = c
  ind2_add : ∀ g h c, ind2 (g + h) c = ind2 h (ind2 g c)
  ind2_inverse : ∀ g c, ind2 (-g) (ind2 g c) = c
  ind3_zero : ∀ c, ind3 0 c = c
  ind3_add : ∀ m n c, ind3 (m + n) c = ind3 n (ind3 m c)
  ind1_ind2_commute : ∀ g h c, ind1 g (ind2 h c) = ind2 h (ind1 g c)
  ind1_ind3_commute : ∀ g n c, ind1 g (ind3 n c) = ind3 n (ind1 g c)
  ind2_ind3_commute : ∀ g n c, ind2 g (ind3 n c) = ind3 n (ind2 g c)
  ind1_level : ∀ g c, level (ind1 g c) = level c
  ind2_level : ∀ g c, level (ind2 g c) = level c
  ind3_level : ∀ n c, level c ≤ level (ind3 n c)
  image_nonempty : ∀ c, (image c).Nonempty
  image_ind1 : ∀ g c, image (ind1 g c) = image c
  image_ind2 : ∀ g c, image (ind2 g c) = image c
  image_ind3 : ∀ m c z, z ∈ image c → ∃ y, y ∈ image (ind3 m c) ∧ z ≤ y
  volume_ind1 : ∀ g c, volume (ind1 g c) = volume c
  volume_ind2 : ∀ g c, volume (ind2 g c) = volume c
  volume_ind3 : ∀ m c, volume c ≤ volume (ind3 m c)

/-- The two-branch image: the down-closed ray `Iic level`. -/
def twoBranchImage (x : Bool × Nat) : Set Real :=
  Set.Iic (x.2 : Real)

/-- The two-branch volume: the level. -/
def twoBranchVolume (x : Bool × Nat) : Real :=
  (x.2 : Real)

/-- The two-branch lift: adds `m` on the `true` branch and `2 * m` on the
`false` branch. -/
def twoBranchInd3 (m : Nat) (x : Bool × Nat) : Bool × Nat :=
  (x.1, x.2 + if x.1 then m else 2 * m)

/-- The level of the two-branch model. -/
def twoBranchLevel (x : Bool × Nat) : Nat :=
  x.2

/-- The lift only raises the level, so it raises the volume. -/
theorem twoBranchVolume_le_ind3 (n : Nat) (c : Bool × Nat) :
    twoBranchVolume c ≤ twoBranchVolume (twoBranchInd3 n c) := by
  have h : c.2 ≤ c.2 + (if c.1 then n else 2 * n) := Nat.le_add_right c.2 _
  have hcast : ((c.2 : Nat) : Real) ≤
      (((c.2 + (if c.1 then n else 2 * n)) : Nat) : Real) := by
    exact_mod_cast h
  simpa [twoBranchVolume, twoBranchInd3] using hcast

/-- The two-branch model satisfies every law of `ImageLiftLawModel`: the
`ind1`/`ind2` actions are identity, the images `Iic level` are preserved by
them, and the domination law holds because the lift only raises the level. -/
def twoBranchModel : ImageLiftLawModel where
  Choice := Bool × Nat
  ind1 := fun _ x => x
  ind2 := fun _ x => x
  ind3 := twoBranchInd3
  level := twoBranchLevel
  image := twoBranchImage
  volume := twoBranchVolume
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun _ => rfl
  ind2_add := fun _ _ _ => rfl
  ind2_inverse := fun _ _ => rfl
  ind3_zero := by
    intro c
    obtain ⟨b, k⟩ := c
    cases b <;> simp [twoBranchInd3]
  ind3_add := by
    intro m n c
    obtain ⟨b, k⟩ := c
    cases b <;> simp [twoBranchInd3] <;> omega
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun n c => by
    have h : c.2 ≤ c.2 + (if c.1 then n else 2 * n) := Nat.le_add_right c.2 _
    exact h
  image_nonempty := fun c => ⟨(c.2 : Real), by simp [twoBranchImage]⟩
  image_ind1 := fun _ _ => rfl
  image_ind2 := fun _ _ => rfl
  image_ind3 := by
    intro m c z hz
    have hz' : z ≤ twoBranchVolume c := hz
    exact ⟨z, le_trans hz' (twoBranchVolume_le_ind3 m c), le_rfl⟩
  volume_ind1 := fun _ _ => rfl
  volume_ind2 := fun _ _ => rfl
  volume_ind3 := twoBranchVolume_le_ind3

/-- The two-branch model violates N2: `(false, 0)` and `(true, 0)` share the
image `Iic 0`, while `ind3 1` sends them to `Iic 2` and `Iic 1`. -/
theorem not_twoBranchModel_ind3ImageWellDefined :
    ¬ (∀ (m : Nat) (c c' : Bool × Nat), twoBranchImage c = twoBranchImage c' →
      twoBranchImage (twoBranchInd3 m c) = twoBranchImage (twoBranchInd3 m c')) := by
  intro h
  have hcc : twoBranchImage (false, 0) = twoBranchImage (true, 0) := by
    simp [twoBranchImage]
  have hbad := h 1 (false, 0) (true, 0) hcc
  have hmem : (2 : Real) ∈ twoBranchImage (twoBranchInd3 1 (false, 0)) := by
    simp [twoBranchImage, twoBranchInd3]
  rw [hbad] at hmem
  simp [twoBranchImage, twoBranchInd3] at hmem

/-- Machine-checked non-derivability of N2 from the frozen laws: there is a
model satisfying every law of `ImageLiftLawModel` in which the Ind3 target
image is not well defined. -/
theorem exists_imageLiftLawModel_not_ind3ImageWellDefined :
    ∃ M : ImageLiftLawModel,
      ¬ (∀ (m : Nat) (c c' : M.Choice), M.image c = M.image c' →
        M.image (M.ind3 m c) = M.image (M.ind3 m c')) := by
  refine ⟨twoBranchModel, ?_⟩
  exact fun hh => not_twoBranchModel_ind3ImageWellDefined hh

/-! ## 6. Status summary (for the audit ledger)

* Leg N1: reduction proved (probe); shape hypothesis and card both refuted on
  the source-audited concrete finite model; frozen-level separation schemas
  proved here.  Status: additional-data.
* Leg A1: reduction proved (probe); shape hypothesis and card both refuted on
  the source-audited concrete finite model; frozen-level separation schemas
  proved here.  Status: additional-data.
* Leg N2: reduction proved (probe); card proved on the concrete finite model
  (singleton route, new here); not derivable from the frozen law fragment
  (two-branch witness, new here).  Status: conditional in general, proved on
  the concrete model.
* Joint route corrected and proved here: down-closed Ind3 targets plus
  unbounded images imply all three cards
  (`k1ImageCards_of_downClosedTargets_unbounded`), through the same frozen
  consumer `k1FromImageCards`
  (`k1VerticalBoundaryOfUnboundedDownClosedTargets`).  The probe's joint
  assembly `k1BoundaryOfEnvelopeConditions` is vacuous
  (`not_envelopeConditions_hypotheses`).
* Consumer mapping: the results feed the K1 six-card route
  (`K1VerticalBoundary`, `CertificateHullWiring`'s K1 import); the hull volume
  finiteness chain (`hull_logVolume_lt_top`, R9) is not addressed here, and
  the corrected regime forces Ind3 target images to be `Set.univ`, so it does
  not supply hull-volume finiteness.
-/

end

end K1K2Realization

end LeanFormal.IUT
