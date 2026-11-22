import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3Reduction
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-!
# Hull presentation alternatives: envelope invariants, sharper separation, hclass descent

Probe file (run `hull-presentation-routes-20261016`, agent Noether).  Read-only
investigation of the `hpres` / `hclass` residuals of `K1K2Realization`; this
file adds declarations only, it modifies no existing file, and it makes no
claim about the original IUT text.  All results below are proved theorems
about the frozen interfaces `SourcePacketRealization`, `LogShellRayPresentation`
and `K1K2BoundaryReduction`; the intended consumers are the hull log-volume
chain (`IQHullLogVolumeInterface`, `CertificateHullWiring`) and the K1 six-card
route (`k1BoundaryOfLogShellPresentation`).

Contents:

* **Sharper separation.**  `hpres` (`LogShellRayPresentation`) fails not only
  for two strictly ordered singleton images
  (`not_logShellRayPresentation_of_two_singletonImages`, existing): any two
  inclusion-incomparable possible images defeat every ray presentation, and a
  ray presentation forces the whole image family to be a chain under inclusion
  (`rayCut_family_image_chain`).  The two-singleton theorem is the
  `v < v'`-special case of `not_logShellRayPresentation_of_incomparable_images`.
* **Envelope presentation.**  For a packet `Q` the envelope
  `imageEnvelope Q c = sSup ((fun z : Real => (z : EReal)) '' Q.possibleImage c)`
  is the canonical complete invariant of the one-sided dominance class: it is
  monotone under `ind3` (`imageEnvelope_ind3_mono`), every image point lies
  below it (`imageEnvelope_upper`), every value strictly below it is dominated
  by an image point (`imageEnvelope_cofinal`), and it is invariant under the
  Ind3 lower closure, which is unified here with Mathlib's set-level
  `lowerClosure` (`possibleImageLowerClosure_carrier`,
  `setEnvelope_lowerClosure`).  The packet law `image_ind3` is exactly the
  lower-closure presentation
  `possibleImage c ⊆ lowerClosure (possibleImage (ind3 m c))`
  (`possibleImage_subset_lowerClosure_ind3`).
* **Toy singleton model.**  `toySingletonImage n = {n}` with the shift
  `ind3 m n = m + n` satisfies the packet domination law and passes the
  lower-closure (envelope) presentation, yet admits no ray presentation at
  all (`not_rayPresentation_toySingleton`): the concrete witness that the
  envelope route bypasses the two-singleton obstruction.
* **hclass descent.**  The volume class preservation
  (`logVolume c = logVolume c' -> logVolume (ind3 m c) = logVolume (ind3 m c')`)
  is exactly the existence of a factor `F m` with
  `logVolume (ind3 m c) = F m (logVolume c)`
  (`valueClassDescent_iff_exists_factor`); a sufficient condition in interface
  vocabulary is a strictly injective functional factorization through the
  procession level together with level-fiber preservation
  (`logVolumeClassDescent_of_level_factorization`).  The constant-shift
  translation law is strictly stronger: the quadratic level model has the
  descent property but no constant shift
  (`quadraticLevelVolume_no_constant_shift`).
* **K1 cards without rays.**  N1 `nonarchimedeanImageInclusion` from
  down-closed Ind3 target images
  (`nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed`), A1
  `archimedeanTargetLift` from unboundedness of the images
  (`archimedeanTargetLift_of_possibleImage_unbounded`), N2
  `ind3ImageWellDefined` from down-closure with attained maxima and a factor
  law for the maxima (`ind3ImageWellDefined_of_attainedMax_factorization`),
  assembled into `K1VerticalBoundary` by `k1BoundaryOfEnvelopeConditions`;
  toy models separate the hypotheses, and the down-closed toy family admits
  no ray presentation at all (`not_Iic_eq_inter_Ici`).
-/

namespace LeanFormal.IUT

universe u v

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. Sharper separation: incomparable images defeat every ray cut -/

/-- The two-singleton separation generalizes: if two possible images are
incomparable under inclusion, *no* ray presentation `S c = L ∩ Set.Ici (h c)`
exists, for any `L` and `h`.  (A ray presentation makes all `L`-ray cuts a
chain, and singletons `{v}`, `{v'}`, `v ≠ v'`, are never comparable.) -/
theorem not_rayCut_family_of_incomparable_images {σ : Type*} (S : σ → Set Real)
    (L : Set Real) (h : σ → Real) {c c' : σ}
    (h1 : ¬ S c ⊆ S c') (h2 : ¬ S c' ⊆ S c) :
    ¬ ∀ c, S c = L ∩ Set.Ici (h c) := by
  intro hray
  rcases le_total (h c) (h c') with hle | hle
  · exact h2 fun z hz => by
      have hz' := hz
      rw [hray c'] at hz'
      rw [hray c]
      exact ⟨hz'.1, le_trans hle hz'.2⟩
  · exact h1 fun z hz => by
      have hz' := hz
      rw [hray c] at hz'
      rw [hray c']
      exact ⟨hz'.1, le_trans hle hz'.2⟩

/-- A ray presentation forces the possible image family to be a chain under
inclusion.  This is the structural reason for the separation: the family of
all `L ∩ Set.Ici x` is totally ordered by inclusion. -/
theorem rayCut_family_image_chain {σ : Type*} (S : σ → Set Real) (L : Set Real)
    (h : σ → Real) (hray : ∀ c, S c = L ∩ Set.Ici (h c)) (c c' : σ) :
    S c ⊆ S c' ∨ S c' ⊆ S c := by
  rcases le_total (h c) (h c') with hle | hle
  · right
    intro z hz
    have hz' := hz
    rw [hray c'] at hz'
    rw [hray c]
    exact ⟨hz'.1, le_trans hle hz'.2⟩
  · left
    intro z hz
    have hz' := hz
    rw [hray c] at hz'
    rw [hray c']
    exact ⟨hz'.1, le_trans hle hz'.2⟩

/-- Packet form of the incomparability separation. -/
theorem not_logShellRayPresentation_of_incomparable_images
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real) {c c' : Choice}
    (h1 : ¬ Q.possibleImage c ⊆ Q.possibleImage c')
    (h2 : ¬ Q.possibleImage c' ⊆ Q.possibleImage c) :
    ¬ LogShellRayPresentation Q L h :=
  not_rayCut_family_of_incomparable_images Q.possibleImage L h h1 h2

/-- Packet form of the chain obstruction. -/
theorem logShellRayPresentation_image_chain {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h) (c c' : Choice) :
    Q.possibleImage c ⊆ Q.possibleImage c' ∨ Q.possibleImage c' ⊆ Q.possibleImage c :=
  rayCut_family_image_chain Q.possibleImage L h hpres c c'

/-- The existing two-singleton separation with the strict order `v < v'`
replaced by the weaker hypothesis `v ≠ v'`. -/
theorem not_logShellRayPresentation_of_distinct_singletonImages
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real) {c c' : Choice} {v v' : Real}
    (hc : Q.possibleImage c = {v}) (hc' : Q.possibleImage c' = {v'}) (hvv' : v ≠ v') :
    ¬ LogShellRayPresentation Q L h := by
  apply not_logShellRayPresentation_of_incomparable_images Q L h
  · intro hsub
    have hv : v ∈ Q.possibleImage c' := hsub (by rw [hc]; exact Set.mem_singleton v)
    rw [hc'] at hv
    exact hvv' (Set.mem_singleton_iff.mp hv)
  · intro hsub
    have hv : v' ∈ Q.possibleImage c := hsub (by rw [hc']; exact Set.mem_singleton v')
    rw [hc] at hv
    exact hvv' (Set.mem_singleton_iff.mp hv).symm

/-! ## 2. Envelope presentation -/

/-- The envelope of a real set: its supremum in `EReal`.  For a possible image
this is the right endpoint of its one-sided dominance class. -/
def setEnvelope (S : Set Real) : EReal :=
  sSup ((fun z : Real => (z : EReal)) '' S)

/-- The packet envelope: the `EReal`-valued right endpoint of a possible
image.  The intended replacement of the height function of a ray
presentation. -/
def imageEnvelope {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (c : Choice) : EReal :=
  setEnvelope (Q.possibleImage c)

theorem imageEnvelope_upper {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (c : Choice) {z : Real}
    (hz : z ∈ Q.possibleImage c) :
    (z : EReal) ≤ imageEnvelope Q c :=
  le_sSup ⟨z, hz, rfl⟩

/-- The envelope is monotone along `ind3` — a consequence of the packet law
`image_ind3`, not a hypothesis. -/
theorem imageEnvelope_ind3_mono {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (m : Nat) (c : Choice) :
    imageEnvelope Q c ≤ imageEnvelope Q (P.ind3 m c) := by
  unfold imageEnvelope setEnvelope
  apply sSup_le
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hzy⟩ := Q.image_ind3 m c z hz
  exact le_trans (EReal.coe_le_coe hzy) (le_sSup ⟨y, hy, rfl⟩)

/-- Cofinality: every value strictly below the envelope is dominated by an
actual image point.  Together with `imageEnvelope_upper` this pins the envelope
as the complete invariant of the dominance class (up to attainment). -/
theorem imageEnvelope_cofinal {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (c : Choice) (z : Real)
    (hz : (z : EReal) < imageEnvelope Q c) :
    ∃ y ∈ Q.possibleImage c, z < y := by
  by_contra h
  have hle : ∀ y ∈ Q.possibleImage c, y ≤ z :=
    fun y hy => le_of_not_gt fun hzy => h ⟨y, hy, hzy⟩
  have hbound : imageEnvelope Q c ≤ (z : EReal) := by
    unfold imageEnvelope setEnvelope
    apply sSup_le
    rintro x ⟨y, hy, rfl⟩
    exact EReal.coe_le_coe (hle y hy)
  exact not_lt.mpr hbound hz

/-- The envelope is invariant under the lower closure (the Ind3 closure of
`PossibleImage.lowerClosure`). -/
theorem setEnvelope_lowerClosure (S : Set Real) :
    setEnvelope ((lowerClosure S : LowerSet Real) : Set Real) = setEnvelope S := by
  apply le_antisymm
  · unfold setEnvelope
    apply sSup_le
    rintro x ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe] at hy
    rw [mem_lowerClosure] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    exact le_trans (EReal.coe_le_coe hyb) (le_sSup ⟨b, hb, rfl⟩)
  · unfold setEnvelope
    apply sSup_le_sSup
    exact Set.image_mono subset_lowerClosure

/-- The envelope is a function of the lower-closure class: it does not change
when the image is replaced by its Ind3 closure. -/
theorem setEnvelope_eq_of_lowerClosure_eq {S T : Set Real}
    (h : ((lowerClosure S : LowerSet Real) : Set Real) =
      ((lowerClosure T : LowerSet Real) : Set Real)) :
    setEnvelope S = setEnvelope T := by
  rw [← setEnvelope_lowerClosure S, h, setEnvelope_lowerClosure T]

/-- The packet law `image_ind3` is exactly the lower-closure presentation of
the image family along the Ind3 chain.  This is the one-sided presentation
that replaces the false ray equality `possibleImage c = L ∩ Set.Ici (h c)`. -/
theorem possibleImage_subset_lowerClosure_ind3 {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (m : Nat) (c : Choice) :
    Q.possibleImage c ⊆
      ((lowerClosure (Q.possibleImage (P.ind3 m c)) : LowerSet Real) : Set Real) :=
  fun z hz => Q.image_ind3 m c z hz

/-- The Ind3 closure of `Ind3Reduction` and Mathlib's set-level lower closure
coincide: the closure operator used by the `(Ind3)` reduction is the closure
operator of the envelope theory. -/
theorem possibleImageLowerClosure_carrier (φ : PossibleImage Real) :
    (PossibleImage.lowerClosure φ).carrier =
      ((lowerClosure φ.carrier : LowerSet Real) : Set Real) := by
  ext z
  constructor
  · intro hz
    exact mem_lowerClosure.mpr (PossibleImage.mem_lowerClosure.mp hz)
  · intro hz
    exact PossibleImage.mem_lowerClosure.mpr (mem_lowerClosure.mp hz)

/-! ## 3. Toy singleton model: envelope presentation without ray presentation -/

/-- The point family `n ↦ {n}` — the value-layer shape of the in-library
singleton image model. -/
def toySingletonImage (n : Nat) : Set Real :=
  {(n : Real)}

/-- The packet domination law holds for the point family under the shift
`ind3 m n = m + n`. -/
theorem toySingletonImage_domination (n m : Nat) :
    ∀ z ∈ toySingletonImage n, ∃ y ∈ toySingletonImage (m + n), z ≤ y := by
  intro z hz
  rw [toySingletonImage, Set.mem_singleton_iff] at hz
  subst hz
  refine ⟨((m + n : Nat) : Real), by simp [toySingletonImage], ?_⟩
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  push_cast
  linarith

/-- The envelope of a point image is the point itself. -/
theorem toySingletonImage_envelope (n : Nat) :
    setEnvelope (toySingletonImage n) = ((n : Real) : EReal) := by
  unfold setEnvelope toySingletonImage
  rw [Set.image_singleton, sSup_singleton]

/-- The point family passes the lower-closure (envelope) presentation. -/
theorem toySingletonImage_subset_lowerClosure_ind3 (n m : Nat) :
    toySingletonImage n ⊆
      ((lowerClosure (toySingletonImage (m + n)) : LowerSet Real) : Set Real) :=
  fun z hz => toySingletonImage_domination n m z hz

/-- Yet no ray presentation exists, for any set `L` and any height `h`: the
envelope presentation strictly dominates the ray presentation on this model. -/
theorem not_rayPresentation_toySingleton (L : Set Real) (h : Nat → Real) :
    ¬ ∀ n, toySingletonImage n = L ∩ Set.Ici (h n) := by
  apply not_rayCut_family_of_incomparable_images toySingletonImage L h
    (c := 0) (c' := 1)
  · intro hsub
    have hmem : (0 : Real) ∈ toySingletonImage 1 := hsub (by simp [toySingletonImage])
    norm_num [toySingletonImage, Set.mem_singleton_iff] at hmem
  · intro hsub
    have hmem : (1 : Real) ∈ toySingletonImage 0 := hsub (by simp [toySingletonImage])
    norm_num [toySingletonImage, Set.mem_singleton_iff] at hmem

/-! ## 4. hclass: value-class descent and the level factorization -/

/-- The general form of the volume class preservation: `ind3` descends along
the fibers of `logVolume` if and only if each `ind3 m` acts on values through a
well-defined function `F m` of the value. -/
theorem valueClassDescent_iff_exists_factor {ι : Type*} (f : ι → Real)
    (g : Nat → ι → ι) :
    (∀ m c c', f c = f c' → f (g m c) = f (g m c')) ↔
      (∀ m, ∃ F : Real → Real, ∀ c, f (g m c) = F (f c)) := by
  constructor
  · intro h m
    classical
    refine ⟨fun r => if hr : ∃ c, f c = r then f (g m hr.choose) else 0, ?_⟩
    intro c
    have hc : ∃ c', f c' = f c := ⟨c, rfl⟩
    change f (g m c) =
      (if hr : ∃ c', f c' = f c then f (g m hr.choose) else 0)
    rw [dif_pos hc]
    exact (h m hc.choose c hc.choose_spec).symm
  · intro hF m c c' hcc'
    obtain ⟨F, hF⟩ := hF m
    rw [hF c, hF c', hcc']

/-- A sufficient condition for value-class descent in interface vocabulary:
`logVolume` factors through the procession level via an injective functional,
and `ind3` acts on level fibers.  The finite model (`ConcreteFiniteModel`,
`normalizedLogVolume_ind3Lift_add`) is an instance with `level = upperSemiLevel`
and `φ l = thetaLogVolume l + l`. -/
theorem valueClassDescent_of_level_factorization {ι : Type*} (f : ι → Real)
    (g : Nat → ι → ι) (level : ι → Nat) (φ : Nat → Real) (hφ : Function.Injective φ)
    (hlvl : ∀ c, f c = φ (level c))
    (hact : ∀ m c c', level c = level c' → level (g m c) = level (g m c')) :
    ∀ m c c', f c = f c' → f (g m c) = f (g m c') := by
  intro m c c' hcc'
  have hl : level c = level c' := hφ (by rw [← hlvl c, ← hlvl c']; exact hcc')
  rw [hlvl (g m c), hlvl (g m c'), hact m c c' hl]

/-- Packet form of the factorization characterization of the volume class
preservation (the `hclass` clause of the six-card table, in volume form). -/
theorem logVolumeClassDescent_iff_exists_factor
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P) :
    (∀ m c c', Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) ↔
      (∀ m, ∃ F : Real → Real, ∀ c, Q.logVolume (P.ind3 m c) = F (Q.logVolume c)) :=
  valueClassDescent_iff_exists_factor Q.logVolume P.ind3

/-- Packet form of the level-factorization sufficient condition, in the
vocabulary of the frozen procession (`P.level`, `P.ind3`). -/
theorem logVolumeClassDescent_of_level_factorization
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (φ : Nat → Real) (hφ : Function.Injective φ)
    (hlvl : ∀ c, Q.logVolume c = φ (P.level c))
    (hact : ∀ m c c', P.level c = P.level c' →
      P.level (P.ind3 m c) = P.level (P.ind3 m c')) :
    ∀ m c c', Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c') :=
  valueClassDescent_of_level_factorization Q.logVolume P.ind3 P.level φ hφ hlvl hact

/-- The `hclass` clause in the negated form consumed by
`k1BoundaryOf_negLogVolumeRayPresentation`, obtained from the level
factorization. -/
theorem hclass_negLogVolume_of_level_factorization
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (φ : Nat → Real) (hφ : Function.Injective φ)
    (hlvl : ∀ c, Q.logVolume c = φ (P.level c))
    (hact : ∀ m c c', P.level c = P.level c' →
      P.level (P.ind3 m c) = P.level (P.ind3 m c')) :
    ∀ m c c', -(Q.logVolume c) = -(Q.logVolume c') →
      -(Q.logVolume (P.ind3 m c)) = -(Q.logVolume (P.ind3 m c')) := by
  intro m c c' hv
  exact congrArg Neg.neg
    (logVolumeClassDescent_of_level_factorization Q φ hφ hlvl hact m c c' (neg_inj.mp hv))

/-- The quadratic level volume: an injective non-affine functional of the
level. -/
def quadraticLevelVolume (n : Nat) : Real :=
  (n : Real) ^ 2

/-- The additive level shift. -/
def quadraticLevelLift (m n : Nat) : Nat :=
  n + m

/-- The quadratic level model has the value-class descent property: the
constant-shift law is *not* needed for `hclass`. -/
theorem quadraticLevelVolume_descent :
    ∀ m n n', quadraticLevelVolume n = quadraticLevelVolume n' →
      quadraticLevelVolume (quadraticLevelLift m n) =
        quadraticLevelVolume (quadraticLevelLift m n') := by
  apply valueClassDescent_of_level_factorization
    (f := quadraticLevelVolume) (g := quadraticLevelLift) (level := id)
    (φ := fun k : Nat => (k : Real) ^ 2)
  · intro a b hab
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hab with hab | hab
    · exact_mod_cast hab
    · have ha : a = 0 := by
        have hna : (0 : Real) ≤ (a : Real) := Nat.cast_nonneg a
        have hnb : (0 : Real) ≤ (b : Real) := Nat.cast_nonneg b
        have h' : (a : Real) = 0 := by nlinarith
        exact_mod_cast h'
      have hb : b = 0 := by
        have hna : (0 : Real) ≤ (a : Real) := Nat.cast_nonneg a
        have hnb : (0 : Real) ≤ (b : Real) := Nat.cast_nonneg b
        have h' : (b : Real) = 0 := by nlinarith
        exact_mod_cast h'
      rw [ha, hb]
  · intro c
    rfl
  · intro m c c' hl
    rw [show c = c' from hl]

/-- The quadratic level model admits no constant shift: the volume translation
law is strictly stronger than `hclass`. -/
theorem quadraticLevelVolume_no_constant_shift :
    ¬ ∃ shift : Nat → Real, ∀ m n,
      quadraticLevelVolume (quadraticLevelLift m n) =
        quadraticLevelVolume n + shift m := by
  rintro ⟨shift, hshift⟩
  have h1 := hshift 1 0
  have h4 := hshift 1 1
  norm_num [quadraticLevelVolume, quadraticLevelLift] at h1 h4
  linarith

/-! ## 5. K1 cards from envelope-side shape conditions (no ray presentation)

The E1 route (`k1BoundaryOfLogShellPresentation` in `SourceK1K2Realization`)
derives the three K1 image cards from the ray presentation
`possibleImage c = L ∩ Set.Ici (h c)`.  That presentation is false in general
(`not_logShellRayPresentation_of_two_singletonImages`; sharper, section 1).
This section replaces the presentation by shape conditions on the images:

* N1 (`nonarchimedeanImageInclusion`): the packet domination law `image_ind3`
  upgrades to set inclusion as soon as the Ind3 target images are down-closed
  in the order of `Real`
  (`nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed`).  The step is the
  `Ind3Reduction` order lemma `le_iff_carrier_subset_of_isLowerClosed` applied
  to the image family read as `PossibleImage Real`.
* A1 (`archimedeanTargetLift`): if every possible image is unbounded above,
  the target lift holds for every real value
  (`archimedeanTargetLift_of_possibleImage_unbounded`); no presentation and no
  membership analysis is used.  The E1 analogue
  (`archimedeanTargetLift_of_logShellPresentation`) needs unboundedness of `L`
  *plus* the presentation.
* N2 (`ind3ImageWellDefined`): if every image is down-closed and attains its
  maximum as a real value, and the attaining maxima of the Ind3 targets are a
  well-defined function of the source maxima, then the Ind3 target images are
  well defined (`ind3ImageWellDefined_of_attainedMax_factorization`); the
  key auxiliary is that a down-closed set with a maximum is the principal
  ideal of that maximum (`eq_Iic_of_isLowerClosed_of_max`).
* The K1 boundary record is assembled from these shape conditions
  (`k1BoundaryOfEnvelopeConditions`), through the same frozen consumer
  `K1K2BoundaryReduction.k1FromImageCards` as the E1 route.

Toy models separate the hypotheses.  The down-closed rays `Set.Iic n`
(`toyDownClosedImage`) satisfy the packet domination law, the N1 shape
hypothesis and the N1 conclusion (`toyDownClosedImage_inclusion`), fail A1
exactly at the level gap (`toyDownClosedImage_lift_fails`) and are not
unbounded (`not_toyDownClosedImage_unbounded`); they allow no ray presentation
at all (`not_Iic_eq_inter_Ici`, `not_rayPresentation_toyDownClosed`).  The
up-closed rays `Set.Ici n` (`toyUpClosedImage`) satisfy domination,
unboundedness and the A1 conclusion (`toyUpClosedImage_lift`), but fail
down-closure (`not_toyUpClosedImage_isLowerClosed`).  Each card therefore has
its own shape hypothesis, independent of the false ray presentation.

Status: conditional reductions.  Under the hypotheses named, the cards and the
boundary record are unconditional theorems of this file; the hypotheses are
not derived here from the arithmetic of log-shells, and the claim that they
hold in the source model is not made. -/

/-- The packet domination law `image_ind3`, read in the `PossibleImage`
one-sided dominance order of `Ind3Reduction`. -/
theorem possibleImage_le_ind3 {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (m : Nat) (c : Choice) :
    (⟨Q.possibleImage c⟩ : PossibleImage Real) ≤
      ⟨Q.possibleImage (P.ind3 m c)⟩ := by
  intro z hz
  exact Q.image_ind3 m c z hz

/-- N1 without the ray presentation: if the Ind3 target images are down-closed
in the order of `Real`, the packet domination law already yields the
nonarchimedean inclusion card.  Compare
`nonarchimedeanImageInclusion_of_logShellPresentation`, which needs the ray
equality plus a height law; here there is no `L`, no `h`, and no equality. -/
theorem nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hclosed : ∀ m c, ∀ ⦃z w : Real⦄,
      w ∈ Q.possibleImage (P.ind3 m c) → z ≤ w →
        z ∈ Q.possibleImage (P.ind3 m c)) :
    K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q := by
  intro m c
  exact (PossibleImage.le_iff_carrier_subset_of_isLowerClosed
    (φ := (⟨Q.possibleImage c⟩ : PossibleImage Real))
    (ψ := (⟨Q.possibleImage (P.ind3 m c)⟩ : PossibleImage Real))
    (hclosed m c)).mp (possibleImage_le_ind3 Q m c)

/-- A1 without the ray presentation: unboundedness of each possible image
dominates every real value, hence in particular the members of the Ind3 target
images.  Compare `archimedeanTargetLift_of_logShellPresentation`, which uses
unboundedness of the carrier set `L` of the presentation; here the ray
equality itself is dropped. -/
theorem archimedeanTargetLift_of_possibleImage_unbounded
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y) :
    K1K2BoundaryReduction.archimedeanTargetLift P Q := by
  intro m c z _
  exact hunb c z

/-- The two image cards N1 and A1 from the two shape hypotheses: down-closure
of the Ind3 targets and unboundedness. -/
theorem k1ImageCards_of_isLowerClosed_unbounded
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hclosed : ∀ m c, ∀ ⦃z w : Real⦄,
      w ∈ Q.possibleImage (P.ind3 m c) → z ≤ w →
        z ∈ Q.possibleImage (P.ind3 m c))
    (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y) :
    K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q ∧
      K1K2BoundaryReduction.archimedeanTargetLift P Q :=
  ⟨nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed Q hclosed,
    archimedeanTargetLift_of_possibleImage_unbounded Q hunb⟩

/-- A down-closed set with a maximum is the principal ideal of that maximum.
Used to show that the attained maximum is a complete invariant of a
down-closed image. -/
theorem eq_Iic_of_isLowerClosed_of_max {S : Set Real} {e : Real}
    (hdown : ∀ ⦃z w : Real⦄, w ∈ S → z ≤ w → z ∈ S) (he : e ∈ S)
    (hmax : ∀ z, z ∈ S → z ≤ e) : S = Set.Iic e := by
  ext z
  exact ⟨fun hz => by simpa using hmax z hz,
    fun hz => hdown (z := z) (w := e) he (by simpa using hz)⟩

/-- The envelope of a principal ideal is its maximum. -/
theorem setEnvelope_Iic (e : Real) : setEnvelope (Set.Iic e) = (e : EReal) := by
  apply le_antisymm
  · unfold setEnvelope
    apply sSup_le
    rintro x ⟨z, hz, rfl⟩
    exact EReal.coe_le_coe (by simpa using hz)
  · unfold setEnvelope
    exact le_sSup ⟨e, le_refl e, rfl⟩

/-- N2 without the ray presentation: if every image is down-closed with an
attained maximum `e` (so each image is the principal ideal of `e`), and the
maxima of the Ind3 targets factor through the source maxima, then the Ind3
target images are well defined.  Compare
`ind3ImageWellDefined_of_logShellPresentation`, which needs the ray equality,
ray separation of `L` and the height-class law; here the separation hypothesis
is replaced by the factor law for the maxima. -/
theorem ind3ImageWellDefined_of_attainedMax_factorization
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (e : Choice → Real)
    (hdown : ∀ c, ∀ ⦃z w : Real⦄, w ∈ Q.possibleImage c → z ≤ w →
      z ∈ Q.possibleImage c)
    (hatt : ∀ c, e c ∈ Q.possibleImage c ∧ ∀ z ∈ Q.possibleImage c, z ≤ e c)
    (hact : ∀ m, ∃ F : Real → Real, ∀ c, e (P.ind3 m c) = F (e c)) :
    K1K2BoundaryReduction.ind3ImageWellDefined P Q := by
  intro m c c' hcc'
  obtain ⟨F, hF⟩ := hact m
  have hcc_eq : e c = e c' :=
    le_antisymm ((hatt c').2 (e c) (hcc' ▸ (hatt c).1))
      ((hatt c).2 (e c') (hcc'.symm ▸ (hatt c').1))
  have hset : ∀ c, Q.possibleImage c = Set.Iic (e c) :=
    fun c => eq_Iic_of_isLowerClosed_of_max (hdown c) (hatt c).1 (hatt c).2
  rw [hset (P.ind3 m c), hset (P.ind3 m c'), hF c, hF c', hcc_eq]

/-- The K1 boundary assembled without any ray presentation, through the same
frozen consumer `K1K2BoundaryReduction.k1FromImageCards` as
`k1BoundaryOfLogShellPresentation`: down-closure, unboundedness and attained
maxima with the factor law replace `(L, h)` and the ray equality.  Reduced
form: inhabitation of the frozen `K1VerticalBoundary` record, not the original
statement of IUT III, Proposition 3.5. -/
def k1BoundaryOfEnvelopeConditions
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hdown : ∀ c, ∀ ⦃z w : Real⦄, w ∈ Q.possibleImage c → z ≤ w →
      z ∈ Q.possibleImage c)
    (hunb : ∀ (c : Choice) (x : Real), ∃ y ∈ Q.possibleImage c, x ≤ y)
    (e : Choice → Real)
    (hatt : ∀ c, e c ∈ Q.possibleImage c ∧ ∀ z ∈ Q.possibleImage c, z ≤ e c)
    (hact : ∀ m, ∃ F : Real → Real, ∀ c, e (P.ind3 m c) = F (e c))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    K1VerticalBoundary P Q :=
  K1K2BoundaryReduction.k1FromImageCards P Q
    (nonarchimedeanImageInclusion_of_ind3Image_isLowerClosed Q
      (fun m c => hdown (P.ind3 m c)))
    (ind3ImageWellDefined_of_attainedMax_factorization Q e hdown hatt hact)
    (archimedeanTargetLift_of_possibleImage_unbounded Q hunb)
    κ

/-! ### 5.1 Toy models separating the shape hypotheses -/

/-- Down-closed rays at level `n`: the bounded model in which the N1 shape
hypothesis holds while the A1 hypotheses fail. -/
def toyDownClosedImage (n : Nat) : Set Real :=
  Set.Iic (n : Real)

/-- The packet domination law holds for the down-closed rays under the shift
`ind3 m n = m + n`. -/
theorem toyDownClosedImage_domination (n m : Nat) :
    ∀ z ∈ toyDownClosedImage n, ∃ y ∈ toyDownClosedImage (m + n), z ≤ y := by
  intro z hz
  refine ⟨z, ?_, le_rfl⟩
  have hzn : z ≤ (n : Real) := by simpa [toyDownClosedImage] using hz
  exact le_trans hzn (by exact_mod_cast Nat.le_add_left n m)

/-- The down-closed rays satisfy the N1 shape hypothesis at every level. -/
theorem toyDownClosedImage_isLowerClosed (k : Nat) :
    PossibleImage.IsLowerClosed (⟨toyDownClosedImage k⟩ : PossibleImage Real) := by
  intro z w hw hzw
  exact le_trans hzw hw

/-- N1 holds in the down-closed model. -/
theorem toyDownClosedImage_inclusion (m n : Nat) :
    toyDownClosedImage n ⊆ toyDownClosedImage (m + n) := by
  intro z hz
  have hzn : z ≤ (n : Real) := by simpa [toyDownClosedImage] using hz
  exact le_trans hzn (by exact_mod_cast Nat.le_add_left n m)

/-- A1 fails in the down-closed model: the level gap `n < m + n` is not
dominated by any point of the lower image. -/
theorem toyDownClosedImage_lift_fails :
    ¬ ∀ (m n : Nat) (z : Real),
      z ∈ toyDownClosedImage (m + n) → ∃ y ∈ toyDownClosedImage n, z ≤ y := by
  intro hCall
  have hmem : (1 : Real) ∈ toyDownClosedImage (1 + 0) := by
    simp [toyDownClosedImage]
  obtain ⟨y, hy, hzy⟩ := hCall 1 0 1 hmem
  have hy' : y ≤ (0 : Real) := by simpa [toyDownClosedImage] using hy
  linarith

/-- The down-closed rays are not unbounded above: the A1 sufficient
hypothesis fails in the same model. -/
theorem not_toyDownClosedImage_unbounded :
    ¬ ∀ (n : Nat) (x : Real), ∃ y ∈ toyDownClosedImage n, x ≤ y := by
  intro hCall
  obtain ⟨y, hy, hxy⟩ := hCall 0 1
  have hy' : y ≤ (0 : Real) := by simpa [toyDownClosedImage] using hy
  linarith

/-- No down-closed unbounded-below set is a ray cut `L ∩ Set.Ici h`: membership
of the maximum `e` forces the ray bound `h ≤ e`, downward membership then
forces `L = Set.Iic e`, and `h - 1 ≤ e < h` would have to lie in the ray. -/
theorem not_Iic_eq_inter_Ici (e : Real) (L : Set Real) (h : Real) :
    Set.Iic e ≠ L ∩ Set.Ici h := by
  intro hEq
  have heS : e ∈ L ∩ Set.Ici h := by
    rw [← hEq]
    exact le_refl e
  have hh : h ≤ e := heS.2
  have hL : L = Set.Iic e := by
    ext y
    constructor
    · intro hy
      by_cases hyh : h ≤ y
      · have hyS : y ∈ L ∩ Set.Ici h := ⟨hy, hyh⟩
        exact hEq.symm ▸ hyS
      · exact le_trans (le_of_lt (not_le.mp hyh)) hh
    · intro hy
      exact (hEq ▸ hy).1
  have hmem : h - 1 ∈ Set.Iic e := by
    rw [Set.mem_Iic]
    linarith
  have hmem' : h - 1 ∈ L ∩ Set.Ici h := hEq ▸ hmem
  have hle : h ≤ h - 1 := by simpa using hmem'.2
  linarith

/-- Consequently the down-closed model admits no ray presentation at all, for
any `L` and any height family: the same conclusion as the singleton model of
section 3, via a different obstruction (bounded-below ray cuts versus
singleton incomparability). -/
theorem not_rayPresentation_toyDownClosed (L : Set Real) (h : Nat → Real) :
    ¬ ∀ n, toyDownClosedImage n = L ∩ Set.Ici (h n) := by
  intro hray
  exact not_Iic_eq_inter_Ici 0 L (h 0)
    (by simpa [toyDownClosedImage] using hray 0)

/-- Up-closed rays at level `n`: the unbounded model in which the A1 shape
hypothesis holds while the N1 shape hypothesis fails. -/
def toyUpClosedImage (n : Nat) : Set Real :=
  Set.Ici (n : Real)

/-- The packet domination law holds for the up-closed rays under the shift
`ind3 m n = m + n`. -/
theorem toyUpClosedImage_domination (n m : Nat) :
    ∀ z ∈ toyUpClosedImage n, ∃ y ∈ toyUpClosedImage (m + n), z ≤ y := by
  intro z _
  refine ⟨max z ((m + n : Nat) : Real), ?_, le_max_left z _⟩
  exact le_max_right z _

/-- The up-closed rays are unbounded above at every level. -/
theorem toyUpClosedImage_unbounded (n : Nat) :
    ∀ x : Real, ∃ y ∈ toyUpClosedImage n, x ≤ y := by
  intro x
  refine ⟨max x (n : Real), ?_, le_max_left x _⟩
  exact le_max_right x _

/-- A1 holds in the up-closed model. -/
theorem toyUpClosedImage_lift (m n : Nat) :
    ∀ z ∈ toyUpClosedImage (m + n), ∃ y ∈ toyUpClosedImage n, z ≤ y := by
  intro z hz
  refine ⟨z, ?_, le_rfl⟩
  have hzt : ((m + n : Nat) : Real) ≤ z := by simpa [toyUpClosedImage] using hz
  exact le_trans (by exact_mod_cast Nat.le_add_left n m) hzt

/-- The up-closed rays fail the N1 shape hypothesis: `0 ≤ 1` with
`1 ∈ Set.Ici 1` does not give `0 ∈ Set.Ici 1`. -/
theorem not_toyUpClosedImage_isLowerClosed :
    ¬ ∀ k : Nat,
      PossibleImage.IsLowerClosed (⟨toyUpClosedImage k⟩ : PossibleImage Real) := by
  intro hCall
  have h1 := hCall 1
  have hmem : (1 : Real) ∈ (⟨toyUpClosedImage 1⟩ : PossibleImage Real) := by
    simp [toyUpClosedImage]
  have hz := h1 (z := (0 : Real)) (w := (1 : Real)) hmem (by norm_num)
  have hz' : (1 : Real) ≤ 0 := by simpa [toyUpClosedImage] using hz
  linarith

end

end K1K2Realization

end LeanFormal.IUT
