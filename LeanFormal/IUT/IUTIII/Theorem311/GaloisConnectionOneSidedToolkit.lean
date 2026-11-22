/-
# One-sided Galois-connection toolkit for the Theorem 3.11 image cards

W2 pilot (wild-brainstorm-20261017.md section 18 W2 entry and section 21 W2
specification, probes A and C, minimal form).  The original statement is the
one-sidedness of (Ind3): IUT III, Theorem 3.11 (III.txt:9151 ff.), (ii)
(corpus III.txt:9439-9446) -- as one varies m, the isomorphisms are only
"upper semi-compatible", with "certain natural inclusions" at the
nonarchimedean vertices and "certain natural surjections" at the
archimedean vertices; the log-volume compatibility is stated separately and
with the stronger "[precisely!]" marker (III.txt:9447-9449).  (The
cross-references ":9600-9612" used in wild-brainstorm sections 20C/21 denote
the same passage; the line count differs, the wording was checked word by
word.)  In the frozen tree the two faces are the cards

* `K1K2BoundaryReduction.nonarchimedeanImageInclusion` (N1, inclusion face,
  K1K2BoundaryReduction.lean:140), and
* `K1K2BoundaryReduction.archimedeanTargetLift` (A1, surjection/lift face,
  K1K2BoundaryReduction.lean:194),

and the lower-envelope presentation (hpres) of the possible images is
`K1K2Realization.LogShellRayPresentation` (SourceK1K2Realization.lean:107):
`possibleImage c` is the log-shell set `L` cut by the height ray at `h c`.

Contents (all on the frozen interfaces above):

1. The lower envelope `setLowerEnvelope` (infimum in `EReal`) forms a literal
   Galois pair with the ray `realRay`: `S` sits inside the ray at `t` exactly
   when `t` is below the envelope of `S`
   (`subset_realRay_iff_le_lowerEnvelope`,
   `galoisConnection_realRay_lowerEnvelope`).  Under hpres: the height is a
   lower bound of the envelope of each image; the forward and inverse ray-cut
   faces are named; and `sInf (possibleImage c) = h c` follows from an
   accumulation hypothesis -- the precise no-gap condition under which hpres
   can be read backwards.
2. The abstract `hull` adjoint `incl` face: every monotone, extensive,
   idempotent operator, with codomain restricted to its fixed points, is the
   lower adjoint of the inclusion of those fixed points
   (`galoisConnection_closure_fixedPoints`); the literal unrestricted reading
   `GaloisConnection H id` degenerates to `H = id`
   (`eq_id_of_galoisConnection_id`); for a closure system the model hull is
   the lower adjoint of the model inclusion and is the minimal model above
   the input (section 4).
3. The composition law of the two one-sided faces across links: the
   single-step cards compose along the cocycle law `P.ind3_add` into the
   composite link; the composite satisfies both faces at once (the sandwich
   law `linkTwoSidedFaces_comp`); the value side carries the upper-semi
   composite `logVolume_ind3_upperSemi_comp` only.  The stronger
   "[precisely!]" log-volume compatibility of the original is not a
   consequence of the frozen packet fields and is not claimed here.

This is a toolkit layer.  No statement of the original text is restated as
proved, and no card is assumed beyond the hypotheses named in each
declaration.
-/
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge

universe u v w

namespace OneSidedGaloisToolkit

noncomputable section

/-! ## 1. Lower envelope and ray: an adjoint pair over `EReal` -/

/-- The ray at an extended threshold, as a set of reals. -/
def realRay (t : EReal) : Set Real := {x : Real | t ≤ (x : EReal)}

/-- The lower envelope of a set of reals: its infimum in `EReal`.  For the
empty set the value is `+inf`, so the adjunction below has no side
condition. -/
def setLowerEnvelope (S : Set Real) : EReal :=
  sInf ((fun x : Real => (x : EReal)) '' S)

/-- The adjunction face: a set sits inside the ray at `t` exactly when `t`
is below its lower envelope. -/
theorem subset_realRay_iff_le_lowerEnvelope (S : Set Real) (t : EReal) :
    S ⊆ realRay t ↔ t ≤ setLowerEnvelope S := by
  constructor
  · intro h
    apply le_sInf
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact h hz
  · intro h z hz
    have h2 : setLowerEnvelope S ≤ (z : EReal) := sInf_le ⟨z, hz, rfl⟩
    exact h.trans h2

/-- The same face as a literal `GaloisConnection` between the ray map and
the lower envelope (with the order dual on the set side). -/
theorem galoisConnection_realRay_lowerEnvelope :
    GaloisConnection (fun t : EReal => OrderDual.toDual (realRay t))
      (fun S : (Set Real)ᵒᵈ => setLowerEnvelope (OrderDual.ofDual S)) := by
  intro a b
  exact subset_realRay_iff_le_lowerEnvelope (OrderDual.ofDual b) a

/-! ## 2. hpres (the E1 ray presentation) through the adjoint face -/

/-- The lower envelope of a possible image of a source packet. -/
def imageLowerEnvelope {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (c : Choice) : EReal :=
  setLowerEnvelope (Q.possibleImage c)

/-- Under hpres the presentation height is a lower bound of the lower
envelope of the image: every element of `possibleImage c` lies in the ray at
`h c`, so the infimum does too.  This one-sided form is the part that is
free; equality needs the accumulation hypothesis of
`sInf_possibleImage_eq_height_of_accumulation`. -/
theorem height_le_imageLowerEnvelope_of_logShellPresentation
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : K1K2Realization.LogShellRayPresentation Q L h) (c : Choice) :
    (h c : EReal) ≤ imageLowerEnvelope Q c := by
  apply le_sInf
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz' := hz
  rw [hpres c] at hz'
  exact EReal.coe_le_coe (Set.mem_Ici.mp hz'.2)

/-- The forward ray-cut face: a cut of `L` at a threshold `a` below the
presentation height `h c` still contains the image. -/
theorem image_subset_rayCut_of_logShellPresentation
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : K1K2Realization.LogShellRayPresentation Q L h)
    {c : Choice} {a : Real} (hca : a ≤ h c) :
    Q.possibleImage c ⊆ L ∩ Set.Ici a := by
  intro z hz
  rw [hpres c] at hz
  exact ⟨hz.1, Set.mem_Ici.mpr (hca.trans (Set.mem_Ici.mp hz.2))⟩

/-- The inverse ray-cut face, free of side conditions: any ray cut of `L`
at a threshold above the presentation height is contained in the image. -/
theorem rayCut_subset_image_of_logShellPresentation
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : K1K2Realization.LogShellRayPresentation Q L h)
    {c : Choice} {t : EReal} (ht : (h c : EReal) ≤ t) :
    L ∩ realRay t ⊆ Q.possibleImage c := by
  intro x hx
  rw [hpres c]
  refine ⟨hx.1, ?_⟩
  have ht' : (h c : EReal) ≤ (x : EReal) := ht.trans hx.2
  exact_mod_cast ht'

/-- Accumulation inverts hpres at the level of readings: if `L` accumulates
at `h c` from above inside the image, then the real infimum of the image is
exactly the presentation height.  Without such accumulation the envelope can
be strictly larger than the presentation height, the same gap phenomenon
that the separation hypothesis of the E1-c card is designed to manage. -/
theorem sInf_possibleImage_eq_height_of_accumulation
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : K1K2Realization.LogShellRayPresentation Q L h) (c : Choice)
    (hacc : ∀ a : Real, h c < a → ∃ y, y ∈ Q.possibleImage c ∧ y < a) :
    sInf (Q.possibleImage c) = h c := by
  have hne : (Q.possibleImage c).Nonempty := Q.possibleImage_nonempty c
  have hbdd : BddBelow (Q.possibleImage c) := by
    refine ⟨h c, ?_⟩
    intro y hy
    have hy' := hy
    rw [hpres c] at hy'
    exact Set.mem_Ici.mp hy'.2
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro eps heps
    obtain ⟨y, hy, hya⟩ := hacc (h c + eps) (by linarith)
    exact (csInf_le hbdd hy).trans hya.le
  · exact le_csInf hne (fun y hy => by
      have hy' := hy
      rw [hpres c] at hy'
      exact Set.mem_Ici.mp hy'.2)

/-! ## 3. Envelope monotonicity under the inclusion face -/

/-- The inclusion face of K1 forces the lower envelope to be antitone along
`ind3`: growing images have smaller infima.  This is the value-side shadow
of card N1 (necessary, not sufficient). -/
theorem imageLowerEnvelope_ind3_le_of_inclusion
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hN1 : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (m : Nat) (c : Choice) :
    imageLowerEnvelope Q (P.ind3 m c) ≤ imageLowerEnvelope Q c := by
  apply le_sInf
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact sInf_le ⟨z, hN1 m c hz, rfl⟩

/-- Composite form of the previous line along the cocycle law: the envelope
at the composite link `m + n` is below the envelope at the source. -/
theorem imageLowerEnvelope_ind3_add_le_of_inclusion
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hN1 : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (m n : Nat) (c : Choice) :
    imageLowerEnvelope Q (P.ind3 (m + n) c) ≤ imageLowerEnvelope Q c := by
  rw [P.ind3_add]
  exact (imageLowerEnvelope_ind3_le_of_inclusion Q hN1 n (P.ind3 m c)).trans
    (imageLowerEnvelope_ind3_le_of_inclusion Q hN1 m c)

/-! ## 4. The abstract `hull` adjoint `incl` face -/

/-- A monotone, extensive, idempotent operator (a closure operator), with
codomain restricted to its fixed points, is the lower adjoint of the
inclusion of those fixed points.  This is the non-degenerate form of the W2
probe A statement; the inclusion carries the "incl" side and the operator
the "hull" side. -/
theorem galoisConnection_closure_fixedPoints {α : Type u} [PartialOrder α]
    (H : α → α) (hmono : Monotone H) (hunit : ∀ a, a ≤ H a)
    (hidem : ∀ a, H (H a) = H a) :
    GaloisConnection (β := {b : α // H b = b})
      (fun a => (⟨H a, hidem a⟩ : {b : α // H b = b}))
      (fun b => (b : α)) := by
  intro a b
  constructor
  · intro hab
    have hab' : H a ≤ (b : α) := hab
    exact (hunit a).trans hab'
  · intro hab
    change H a ≤ (b : α)
    calc H a ≤ H (b : α) := hmono hab
      _ = (b : α) := b.2

/-- The literal unrestricted reading of probe A, `GaloisConnection H id`,
degenerates: it forces `H = id`.  The non-degenerate content is the
fixed-point form above. -/
theorem eq_id_of_galoisConnection_id {α : Type u} [PartialOrder α] (H : α → α)
    (h : GaloisConnection H id) : ∀ a, H a = a := by
  intro a
  exact le_antisymm ((h a a).mpr le_rfl) ((h a (H a)).mp le_rfl)

/-- The model hull: the infimum of the models above the input. -/
def modelHull {α : Type u} [CompleteLattice α] (models : Set α) (x : α) : α :=
  sInf {y | y ∈ models ∧ x ≤ y}

/-- The model hull of any input is again a model, for a closure system. -/
theorem modelHull_mem {α : Type u} [CompleteLattice α] {models : Set α}
    (hA : ∀ s : Set α, s ⊆ models → sInf s ∈ models) (x : α) :
    modelHull models x ∈ models :=
  hA _ (by intro y hy; exact hy.1)

/-- Minimality: the model hull is below every model above the input.  This
is the abstract form of "hull = the minimal extension". -/
theorem modelHull_minimal {α : Type u} [CompleteLattice α] {models : Set α}
    (hA : ∀ s : Set α, s ⊆ models → sInf s ∈ models) {x y : α}
    (hy : y ∈ models) (hxy : x ≤ y) :
    modelHull models x ≤ y :=
  sInf_le ⟨hy, hxy⟩

/-- The adjunction face on models: below a model, the hull can be dropped. -/
theorem modelHull_le_iff {α : Type u} [CompleteLattice α] {models : Set α}
    (hA : ∀ s : Set α, s ⊆ models → sInf s ∈ models) {x y : α}
    (hy : y ∈ models) :
    modelHull models x ≤ y ↔ x ≤ y := by
  constructor
  · intro h
    exact (le_sInf (by intro b hb; exact hb.2)).trans h
  · intro h
    exact modelHull_minimal hA hy h

/-- The model hull as a literal `GaloisConnection`: the hull is the lower
adjoint of the inclusion of the models. -/
theorem modelHull_galoisConnection {α : Type u} [CompleteLattice α]
    {models : Set α}
    (hA : ∀ s : Set α, s ⊆ models → sInf s ∈ models) :
    GaloisConnection
      (fun x : α =>
        (⟨modelHull models x, modelHull_mem hA x⟩ : {y : α // y ∈ models}))
      (fun y : {y : α // y ∈ models} => (y : α)) := by
  intro x y
  constructor
  · intro h
    have h' : modelHull models x ≤ (y : α) := h
    exact (le_sInf (by intro b hb; exact hb.2)).trans h'
  · intro h
    change modelHull models x ≤ (y : α)
    exact modelHull_minimal hA y.2 h

/-- Models are fixed points of the model hull (the "whole model is fixed"
face of probe A). -/
theorem modelHull_of_mem {α : Type u} [CompleteLattice α] {models : Set α}
    (hA : ∀ s : Set α, s ⊆ models → sInf s ∈ models) {y : α}
    (hy : y ∈ models) :
    modelHull models y = y :=
  le_antisymm (modelHull_minimal hA hy le_rfl)
    (le_sInf (by intro b hb; exact hb.2))

/-! ## 5. The composition law of the two one-sided faces -/

/-- The inclusion face composes along the cocycle law `ind3_add`: the
single-step card for `m` and `n` gives the composite-parameter card. -/
theorem nonarchimedeanImageInclusion_comp
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hN1 : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (m n : Nat) (c : Choice) :
    Q.possibleImage c ⊆ Q.possibleImage (P.ind3 (m + n) c) := by
  rw [P.ind3_add]
  exact (hN1 m c).trans (hN1 n (P.ind3 m c))

/-- The lift face composes the same way, in reverse: the composite target
image is dominated by the source image. -/
theorem archimedeanTargetLift_comp
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hA1 : K1K2BoundaryReduction.archimedeanTargetLift P Q)
    (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage (P.ind3 (m + n) c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  rw [P.ind3_add] at hz
  obtain ⟨y1, hy1, hzy1⟩ := hA1 n (P.ind3 m c) z hz
  obtain ⟨y, hy, hy1y⟩ := hA1 m c y1 hy1
  exact ⟨y, hy, hzy1.trans hy1y⟩

/-- The sandwich law: at the composite link both faces hold at once. -/
theorem linkTwoSidedFaces_comp
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hN1 : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hA1 : K1K2BoundaryReduction.archimedeanTargetLift P Q)
    (m n : Nat) (c : Choice) :
    Q.possibleImage c ⊆ Q.possibleImage (P.ind3 (m + n) c) ∧
      (∀ z : Real, z ∈ Q.possibleImage (P.ind3 (m + n) c) →
        ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y) :=
  ⟨nonarchimedeanImageInclusion_comp Q hN1 m n c,
    fun z hz => archimedeanTargetLift_comp Q hA1 m n c z hz⟩

/-- The value side composes as upper semi only: the frozen packet carries the
one-sided law `logVolume c ≤ logVolume (ind3 n c)`, and its composite is the
same inequality at the composite parameter.  The "[precisely!]"
log-volume compatibility of the original concerns the mutual compatibility
of the isomorphisms themselves and is not a consequence of these fields. -/
theorem logVolume_ind3_upperSemi_comp
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (m n : Nat) (c : Choice) :
    Q.logVolume c ≤ Q.logVolume (P.ind3 (m + n) c) := by
  rw [P.ind3_add]
  exact (Q.ind3_volume m c).trans (Q.ind3_volume n (P.ind3 m c))

end

end OneSidedGaloisToolkit

end LeanFormal.IUT
