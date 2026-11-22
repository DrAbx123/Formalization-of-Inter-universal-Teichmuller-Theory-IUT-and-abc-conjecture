/-
  # Source image sets and the holomorphic hull of Theorem 3.11 / Corollary 3.12

  This module constructs, from the *actual* original input contract
  `Theorem311Source.OriginalInput` (IUT III Theorem 3.11 opening quantifiers) and the
  *actual* theta special values carried by that input, the source image data to which
  Corollary 3.12 applies its holomorphic hull:

  * the local value monoid `Mon v` of the prime strip of each source theater, with its
    genuine `Pi v`-action and its `Multiplicative Real` degree homomorphism;
  * a source realization of the positive reals in the value monoid at `v` — the
    value-group embedding through which the `q`-parameters and the finite étale theta
    special values enter the log-shell; it is a monoid homomorphism, and its value at
    the `q`-parameter is required to be faithful for the degree;
  * the global (multiplicative) point carrier
    `ThetaPilotPoint := (ThetaPilotCarrier x SignedLabel) -> Mon v`, the value-monoid
    realization of the tensor product of the local value monoids at the indexed
    places, labeled by the finite `j ∈ F_l^⋇`;
  * the family of possible theta-pilot images, indexed by the processions `n` of the
    fixed theta-pilot carrier, and the union of that family;
  * the holomorphic hull of that union, defined as the least candidate hull (a
    submonoid stable under every scaling whose components are all nonzero), i.e.
    exactly the paper's `phi(P) = ⋂_{H ∋ H ⊇ P} H` characterization
    (Remark 3.9.5, (i), (ii)).

  The paper's `lambda · O` hulls live inside the inductive-system carrier
  `IQ(S±_{j+1}; n,◦D⊢_{vQ})` with its log-shell and its Haar log-volume; those objects
  are **not** fields of `OriginalInput`.  What is formalized here is the value-monoid
  (localization) realization of the hull operation together with the universal
  property that the paper itself proves for it.  The module is explicit about the
  missing source interface; see `LiteralArithmeticHullInterface` and
  `literalHullInterface_impossible` below.

  Source correspondence: IUT III, Remark 3.9.5, (i), (ii); Corollary 3.12 statement
  and proof (the `n,◦U_{j,vQ}` and their hulls); Remark 3.9.4 (`O_k^× ⊆ k`,
  `log_k(O_k^×) ⊆ k`).
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui uMon

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 0. The labeled theta-pilot carrier -/

/-- The finite carrier of theta-pilot processions used by the fixed one-column
presentation of Corollary 3.12: the stages `0, …, l*` of the `n`-procession. -/
def ThetaPilotCarrier (l : PrimeGeFive) : Type :=
  Fin (lStar l.value + 1)

/-- The zero label `j = 0` of the finite label set `F_l^⋇`.  It is the label of the
theta-pilot object at `(0,0)` in the statement of Corollary 3.12 itself. -/
def zeroSignedLabel : SignedLabel l.value :=
  ⟨0, by
    have h : (0 : Int) ≤ (lStar l.value : Int) := by
      exact_mod_cast Nat.zero_le (lStar l.value)
    exact ⟨by omega, h⟩⟩

theorem zeroSignedLabel_val : (zeroSignedLabel (l := l)).1 = 0 :=
  rfl

/-! ## 1. The local value monoid and its degree -/

/-- The local value monoid of the prime strip of the theater at `(n,m)`, at the
place `v`.  This is the actual `FPrimeStrip.Mon v` carried by the source input. -/
abbrev ValueMonoidAt (n m : Int) (v : V) : Type umon :=
  (I.primeStripAt n m).Mon v

/-- The theta special value at `(n,m)` and label `j`, read from the actual
`FiniteThetaPacket` of the source theater at `(n,m)` (IUT II theta special values). -/
def thetaValueAt (n m : Int) (j : SignedLabel l.value) : Real :=
  (I.theaterAt n m).thetaPacket.scale j

theorem thetaValueAt_pos (n m : Int) (j : SignedLabel l.value) :
    0 < I.thetaValueAt n m j :=
  (I.theaterAt n m).thetaPacket.scale_pos j

theorem thetaValueAt_ne_zero (n m : Int) (j : SignedLabel l.value) :
    I.thetaValueAt n m j ≠ 0 :=
  ne_of_gt (I.thetaValueAt_pos n m j)

/-- The real logarithm of a local value, via the genuine degree homomorphism
`Mon v →* Multiplicative Real` of the source prime strip. -/
def logDegreeAt (n m : Int) (v : V) (x : I.ValueMonoidAt n m v) : Real :=
  Multiplicative.toAdd ((I.primeStripAt n m).degree v x)

theorem logDegreeAt_mul (n m : Int) (v : V)
    (x y : I.ValueMonoidAt n m v) :
    I.logDegreeAt n m v (x * y) =
      I.logDegreeAt n m v x + I.logDegreeAt n m v y := by
  unfold logDegreeAt
  rw [map_mul]
  rfl

theorem logDegreeAt_one (n m : Int) (v : V) :
    I.logDegreeAt n m v 1 = 0 := by
  unfold logDegreeAt
  rw [map_one]
  rfl

instance valueMonoidAtCommMonoid (n m : Int) (v : V) :
    CommMonoid (I.ValueMonoidAt n m v) :=
  (I.primeStripAt n m).commMonoidMon v

/-- The monoid element attached to a positive real theta value: the value-group
element `exp_add (log x)`.  This is `x` itself in multiplicative notation, expressed
through the exponent so that it lives in `Multiplicative ℝ`. -/
def thetaValueMonoidElement (n m : Int) (j : SignedLabel l.value) :
    Multiplicative Real :=
  Multiplicative.ofAdd (Real.log (I.thetaValueAt n m j))

theorem thetaValueMonoidElement_eq_ofAdd (n m : Int) (j : SignedLabel l.value) :
    I.thetaValueMonoidElement n m j =
      Multiplicative.ofAdd (Real.log (I.thetaValueAt n m j)) :=
  rfl

/-! ## 2. The global value point carrier -/

/-- The global value point carrier: for every theta-pilot procession `n` and every
signed label `j`, one local value at the place `v`.  This is the value-monoid
realization of the `v`-component of the tensor packet of the multiradial
representation of Theorem 3.11, (i). -/
abbrev ThetaPilotPoint (v : V) : Type umon :=
  ThetaPilotCarrier l × SignedLabel l.value → (I.primeStripAt 0 0).Mon v

/-- The global value point carrier is a commutative monoid, componentwise. -/
instance thetaPilotPointCommMonoid (v : V) :
    CommMonoid (I.ThetaPilotPoint v) :=
  inferInstance

/-! ## 3. The source realization of the positive reals in the value monoid

The finite étale theta special values `q_v^{j²}` and the `q`-parameters themselves
are positive reals, and they enter the log-shell through the value-group portion of
the log-Kummer correspondence (Remark 3.9.4: `O_k^× × q^ℕ ⊆ k`,
`log_k(O_k^×) ⊆ k`).  The structure below records exactly that entry point as a
monoid homomorphism `Multiplicative ℝ →* Mon v`, required to be faithful for the
degree at the `q`-parameter.  It is *not* a surrender of the theta image data to a
free parameter: the argument at which it is evaluated is always the actual
`FiniteThetaPacket.scale j` of the actual source theater. -/

/-- The source realization of positive real value data in the local value monoid at
the place `v`, with the degree faithfulness at `q` that makes it the value-group
embedding of the log-shell discussion of Remark 3.9.4. -/
structure SourceImageRealization (v : V) where
  /-- The value-group realization of the positive reals: `x ↦ x` in multiplicative
  notation. -/
  posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 v
  /-- The realized `q`-parameter has the `q`-log, which is the `v ∈ V^bad`
  normalization of Remark 3.9.4, (iv). -/
  degree_of_q : I.logDegreeAt 0 0 v
      (posRealAction (Multiplicative.ofAdd (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
    Real.log ((I.theaterAt 0 0).thetaPacket.q)

/-- The value-group element of the actual theta special value of the source packet
at `(n,0)` and label `j`, at the place `v`. -/
def thetaImageValue (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) : I.ValueMonoidAt 0 0 v :=
  R.posRealAction (I.thetaValueMonoidElement (n.1 : Int) 0 j)

theorem thetaImageValue_eq (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.thetaImageValue R n j =
      R.posRealAction
        (Multiplicative.ofAdd (Real.log (I.thetaValueAt (n.1 : Int) 0 j))) :=
  rfl

/-! ## 4. The source theta-pilot image points -/

/-- The constant global point with value the realization of `x`. -/
def constantThetaPilotPoint (v : V) (R : I.SourceImageRealization v)
    (x : Multiplicative Real) : I.ThetaPilotPoint v :=
  fun _ => R.posRealAction x

theorem constantThetaPilotPoint_apply (v : V) (R : I.SourceImageRealization v)
    (x : Multiplicative Real)
    (p : ThetaPilotCarrier l × SignedLabel l.value) :
    I.constantThetaPilotPoint v R x p = R.posRealAction x :=
  rfl

/-- The actual theta-pilot point of the source at procession `n`, place `v`, label
`j`: the value-group element of the actual theta special value of the source
packet, placed on every component of the global carrier.  The source links make the
choice of theater inside the column immaterial (Theorem 3.11, (i)). -/
def sourceThetaPilotPoint (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) : I.ThetaPilotPoint v :=
  fun _ => I.thetaImageValue R n j

theorem sourceThetaPilotPoint_apply (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value)
    (p : ThetaPilotCarrier l × SignedLabel l.value) :
    I.sourceThetaPilotPoint v R n j p = I.thetaImageValue R n j :=
  rfl

/-- The `v`-component of the possible image of the theta-pilot object at
procession `n` labeled by `j`: the value-realized singleton image set. -/
def sourceThetaPilotImageAt (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    Set (I.ThetaPilotPoint v) :=
  {I.sourceThetaPilotPoint v R n j}

/-! ## 4. The union of possible theta-pilot images -/

/-- A point of the ambient value carrier is in the union of possible images of a
theta-pilot object (relative to the relevant Kummer isomorphisms of Theorem 3.11,
(ii), in the multiradial representation of Theorem 3.11, (i)) if it is the image
point of some signed label.  This is the value-realized transcription of the union
`⋃_{j} n,◦U_{j,vQ}` of Corollary 3.12. -/
def PossibleThetaPilotImageAt (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint v) : Prop :=
  ∃ j : SignedLabel l.value, x = I.sourceThetaPilotPoint v R n j

/-- The union of the possible images of a theta-pilot object at procession `n`,
at the local place `v`: the value-realized `n,◦U_{vQ}` of Corollary 3.12. -/
def possibleThetaPilotImageSet (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Set (I.ThetaPilotPoint v) :=
  {x | I.PossibleThetaPilotImageAt v R n x}

theorem mem_possibleThetaPilotImageSet_iff (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint v) :
    x ∈ I.possibleThetaPilotImageSet v R n ↔
      ∃ j : SignedLabel l.value, x = I.sourceThetaPilotPoint v R n j :=
  Iff.rfl

theorem sourceThetaPilotPoint_mem (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.sourceThetaPilotPoint v R n j ∈ I.possibleThetaPilotImageSet v R n :=
  ⟨j, rfl⟩

theorem possibleThetaPilotImageSet_nonempty (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    (I.possibleThetaPilotImageSet v R n).Nonempty :=
  ⟨I.sourceThetaPilotPoint v R n zeroSignedLabel,
    sourceThetaPilotPoint_mem (I := I) v R n _⟩

/-! ## 5. The hull operation: candidate hulls and the least one

The paper's Remark 3.9.5, (i), defines the holomorphic hull of `αU` to be the
smallest subset of the form `αH = λ·O_{αF_vQ}` (each component of `λ` nonzero) that
contains `αU`.  At the value-monoid level, `O` is the whole ambient monoid and `λ`
is a scaling; a subset of the form `λ·O` is then precisely a subset stable under
multiplication by every scaling.  Remark 3.9.5, (ii), proves that this operation is
the map `φ(P) = ⋂_{H ∋ H ⊇ P} H`.  Both are formalized here. -/

/-- The multiplicative action of a scaling on an ambient value point: componentwise
multiplication, the value-realized form of `x ↦ λ · x` in Remark 3.9.5, (i). -/
def scaleAction {P : Type uMon} [CommMonoid P] (s : P) (x : P) : P :=
  s * x

theorem scaleAction_mul {P : Type uMon} [CommMonoid P] (s t x : P) :
    scaleAction (s * t) x = scaleAction s (scaleAction t x) := by
  simp [scaleAction, mul_assoc]

theorem scaleAction_one {P : Type uMon} [CommMonoid P] (x : P) :
    scaleAction (1 : P) x = x := by
  simp [scaleAction]

/-- The `λ · O` region of Remark 3.9.5, (i) in the value realization: the
multiplicative image of a set of ambient value points under the scaling `λ`.  These are
the regions whose least hull is taken in the proof of Corollary 3.12. -/
def scaledRegionImage {P : Type uMon} [CommMonoid P] (lam : P) (O : Set P) : Set P :=
  {x | ∃ y ∈ O, x = lam * y}

theorem mem_scaledRegionImage_iff {P : Type uMon} [CommMonoid P] {lam : P}
    {O : Set P} {x : P} :
    x ∈ scaledRegionImage lam O ↔ ∃ y ∈ O, x = lam * y :=
  Iff.rfl

theorem scaledRegionImage_mono {P : Type uMon} [CommMonoid P] {lam : P}
    {O O' : Set P} (h : O ⊆ O') :
    scaledRegionImage lam O ⊆ scaledRegionImage lam O' := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

/-- The hull condition of Remark 3.9.5, (i): a submonoid that is stable under
multiplication by every scaling, i.e. a union of subsets of the form `λ·O`.  The
paper's `H ⊆ P` (hulls are direct product regions) is the corresponding
ambient-regularity condition, which in the value realization is carried by the
ambient carrier itself. -/
def CandidateHull {P : Type uMon} [CommMonoid P] (Scaling : Set P)
    (H : Submonoid P) : Prop :=
  ∀ s : P, s ∈ Scaling → ∀ x : P, x ∈ H → s * x ∈ H

theorem candidateHull_top {P : Type uMon} [CommMonoid P] (Scaling : Set P) :
    CandidateHull Scaling (⊤ : Submonoid P) := by
  intro s _ x _
  exact Submonoid.mem_top (s * x)

/-- If every scaling already lies in a set `C` and `C` is stable under
multiplication by scalings, then `C` is a candidate hull.  This is the elementary
form of the hull condition used when comparing candidate hulls. -/
theorem candidateHull_of_scaling_subset {P : Type uMon} [CommMonoid P]
    {Scaling : Set P} {C : Set P} (hScaling : Scaling ⊆ C)
    (hC : ∀ s : P, s ∈ Scaling → ∀ x : P, x ∈ C → s * x ∈ C) :
    ∀ H : Submonoid P, ((H : Set P) = C) → CandidateHull Scaling H := by
  intro H hH s hs x hx
  have hxC : x ∈ C := by
    rw [← hH]
    exact hx
  have hmulC : s * x ∈ C := hC s hs x hxC
  rw [← hH] at hmulC
  exact hmulC

/-- The least candidate hull containing a set: the intersection of all candidate
hulls containing it.  This is the paper's `φ(P) = ⋂_{H ∋ H ⊇ P} H`
(Remark 3.9.5, (ii)), expressed with submonoid intersection. -/
def holomorphicHull {P : Type uMon} [CommMonoid P] (Scaling : Set P)
    (S : Set P) : Submonoid P :=
  ⨅ H : {H : Submonoid P // CandidateHull Scaling H ∧ S ⊆ (H : Set P)},
    (H.1 : Submonoid P)

theorem mem_holomorphicHull_iff {P : Type uMon} [CommMonoid P] {Scaling : Set P}
    {S : Set P} {x : P} :
    x ∈ holomorphicHull Scaling S ↔
      ∀ H : Submonoid P, CandidateHull Scaling H → S ⊆ (H : Set P) → x ∈ H := by
  constructor
  · intro hx H hH hS
    exact Submonoid.mem_iInf.mp hx ⟨H, hH, hS⟩
  · intro hx
    exact Submonoid.mem_iInf.mpr fun H => hx H.1 H.2.1 H.2.2

theorem subset_holomorphicHull {P : Type uMon} [CommMonoid P] {Scaling : Set P}
    {S : Set P} : S ⊆ (holomorphicHull Scaling S : Set P) := by
  intro x hx
  exact (mem_holomorphicHull_iff (Scaling := Scaling) (S := S)).mpr
    (fun _ _ hS => hS hx)

theorem holomorphicHull_candidateHull {P : Type uMon} [CommMonoid P]
    {Scaling : Set P} {S : Set P} :
    CandidateHull Scaling (holomorphicHull Scaling S) := by
  intro s hs x hx
  rw [mem_holomorphicHull_iff] at hx ⊢
  intro H hH hS
  exact hH s hs x (hx H hH hS)

theorem holomorphicHull_le {P : Type uMon} [CommMonoid P] {Scaling : Set P}
    {S : Set P} {H : Submonoid P} (hH : CandidateHull Scaling H)
    (hS : S ⊆ (H : Set P)) :
    holomorphicHull Scaling S ≤ H := by
  intro x hx
  exact (mem_holomorphicHull_iff (Scaling := Scaling) (S := S)).mp hx H hH hS

theorem le_holomorphicHull_of_le {P : Type uMon} [CommMonoid P] {Scaling : Set P}
    {S T : Set P} (hST : S ⊆ T) :
    holomorphicHull Scaling S ≤ holomorphicHull Scaling T := by
  refine holomorphicHull_le holomorphicHull_candidateHull ?_
  intro x hx
  exact subset_holomorphicHull (hST hx)

theorem holomorphicHull_eq_self {P : Type uMon} [CommMonoid P] {Scaling : Set P}
    {H : Submonoid P} (hH : CandidateHull Scaling H) :
    holomorphicHull Scaling (H : Set P) = H := by
  refine le_antisymm (holomorphicHull_le hH (fun x hx => hx)) ?_
  exact subset_holomorphicHull

theorem holomorphicHull_idempotent {P : Type uMon} [CommMonoid P]
    {Scaling : Set P} (S : Set P) :
    holomorphicHull Scaling (holomorphicHull Scaling S : Set P) =
      holomorphicHull Scaling S :=
  holomorphicHull_eq_self holomorphicHull_candidateHull

/-- The paper's `φ(H) = H` (P1), `P ⊆ φ(P)` (P2) and monotonicity (P3)
(Remark 3.9.5, (ii)) hold for the least candidate hull. -/
theorem holomorphicHull_paper_properties {P : Type uMon} [CommMonoid P]
    {Scaling : Set P} :
    (∀ H : Submonoid P, CandidateHull Scaling H →
        holomorphicHull Scaling (H : Set P) = H) ∧
      (∀ S : Set P, S ⊆ (holomorphicHull Scaling S : Set P)) ∧
      (∀ S T : Set P, S ⊆ T →
        holomorphicHull Scaling S ≤ holomorphicHull Scaling T) :=
  ⟨fun _ hH => holomorphicHull_eq_self hH,
    fun _ => subset_holomorphicHull,
    fun _ _ hST => le_holomorphicHull_of_le hST⟩

/-! ## 6. The concrete source hull of the union of possible images -/

/-- The scalings of the hull operation for the source: those global value points
every one of whose components is nonzero (the paper's `λ` with all components
nonzero, Remark 3.9.5, (i)).  In the value monoid a nonzero component is a
component different from the trivial unit. -/
def sourceScalingUnits (v : V) : Set (I.ThetaPilotPoint v) :=
  {s | ∀ p : ThetaPilotCarrier l × SignedLabel l.value, s p ≠ 1}

/-- The holomorphic hull of the union of possible theta-pilot images at procession
`n` and place `v`: the least candidate hull containing the value-realized
`n,◦U_{vQ}`.  This is the transcription of the `n,◦U_{j,vQ}` hulls of the proof of
Corollary 3.12 at the value-monoid level. -/
def sourceHolomorphicHull (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Submonoid (I.ThetaPilotPoint v) :=
  holomorphicHull (I.sourceScalingUnits v) (I.possibleThetaPilotImageSet v R n)

theorem possibleThetaPilotImage_subset_sourceHolomorphicHull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  subset_holomorphicHull

theorem sourceHolomorphicHull_candidate (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    CandidateHull (I.sourceScalingUnits v) (I.sourceHolomorphicHull v R n) :=
  holomorphicHull_candidateHull

theorem sourceHolomorphicHull_le (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) {H : Submonoid (I.ThetaPilotPoint v)}
    (hH : CandidateHull (I.sourceScalingUnits v) H)
    (hS : I.possibleThetaPilotImageSet v R n ⊆ (H : Set (I.ThetaPilotPoint v))) :
    I.sourceHolomorphicHull v R n ≤ H :=
  holomorphicHull_le hH hS

theorem sourceHolomorphicHull_eq_self (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) {H : Submonoid (I.ThetaPilotPoint v)}
    (hH : CandidateHull (I.sourceScalingUnits v) H) :
    holomorphicHull (I.sourceScalingUnits v)
        (H : Set (I.ThetaPilotPoint v)) = H :=
  holomorphicHull_eq_self hH

theorem sourceHolomorphicHull_idempotent (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    holomorphicHull (I.sourceScalingUnits v)
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) =
      I.sourceHolomorphicHull v R n :=
  holomorphicHull_idempotent _

theorem sourceHolomorphicHull_monotone (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceHolomorphicHull v R n ≤ I.sourceHolomorphicHull v R n :=
  le_rfl

/-- The source hull operation satisfies the paper's characterizing properties
(P1), (P2), and monotonicity at the level of the actual theta-pilot image sets. -/
theorem sourceHolomorphicHull_paper_properties (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (∀ H : Submonoid (I.ThetaPilotPoint v),
        CandidateHull (I.sourceScalingUnits v) H →
        holomorphicHull (I.sourceScalingUnits v)
          (H : Set (I.ThetaPilotPoint v)) = H) ∧
      I.possibleThetaPilotImageSet v R n ⊆
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
      (I.sourceHolomorphicHull v R n ≤ I.sourceHolomorphicHull v R n) :=
  ⟨fun _ hH => holomorphicHull_eq_self hH,
    possibleThetaPilotImage_subset_sourceHolomorphicHull (I := I) v R n,
    le_rfl⟩

/-- The source hull is a submonoid, so it contains the product of any two of its
elements; this is the value-level form of "λ·O is closed under multiplication". -/
theorem sourceHolomorphicHull_mul_mem (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) {x y : I.ThetaPilotPoint v}
    (hx : x ∈ I.sourceHolomorphicHull v R n)
    (hy : y ∈ I.sourceHolomorphicHull v R n) :
    x * y ∈ I.sourceHolomorphicHull v R n :=
  (I.sourceHolomorphicHull v R n).mul_mem hx hy

theorem sourceHolomorphicHull_one_mem (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    (1 : I.ThetaPilotPoint v) ∈ I.sourceHolomorphicHull v R n :=
  (I.sourceHolomorphicHull v R n).one_mem

/-! ## 7. Stability of the hull under the source scalings -/

theorem holomorphicHull_scaling_mem {P : Type uMon} [CommMonoid P]
    {Scaling : Set P} {S : Set P} {s : P} (hs : s ∈ Scaling) {x : P}
    (hx : x ∈ holomorphicHull Scaling S) :
    s * x ∈ holomorphicHull Scaling S :=
  holomorphicHull_candidateHull s hs x hx

theorem sourceHolomorphicHull_scaling_mem (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) {s : I.ThetaPilotPoint v}
    (hs : s ∈ I.sourceScalingUnits v) {x : I.ThetaPilotPoint v}
    (hx : x ∈ I.sourceHolomorphicHull v R n) :
    s * x ∈ I.sourceHolomorphicHull v R n :=
  sourceHolomorphicHull_candidate (I := I) v R n s hs x hx

/-- Every image point of the theta-pilot object lies in the source hull. -/
theorem sourceThetaPilotPoint_mem_sourceHolomorphicHull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    I.sourceThetaPilotPoint v R n j ∈ I.sourceHolomorphicHull v R n :=
  possibleThetaPilotImage_subset_sourceHolomorphicHull (I := I) v R n
    (I.sourceThetaPilotPoint_mem v R n j)

/-! ## 8. The literal paper interface and the exact source gap

Corollary 3.12's finiteness argument for `−|log(Θ)|` uses, in the paper's own
words, "the compactness of the `1,◦U_{j,vQ}`, together with the definition of the
log-volume".  Neither the ambient inductive-system carrier
`IQ(S±_{j+1}; n,◦D⊢_{vQ})`, nor its log-shell/ring-of-integers sublattice, nor
compactness of the image sets, nor the Haar log-volume functional is a field of
`OriginalInput`.  The predicate and structure below name exactly the missing part;
the theorem after them records that the pure hull form *does* admit the empty set,
so the nondegeneracy that the paper needs is an extra input and cannot be recovered
from the hull operation alone. -/

/-- The paper's hulls of Remark 3.9.5, (i), literally: subsets of the form `λ·O`
with every component of `λ` nonzero (constructor `scaled`), together with the whole
ambient (`λ = 1`).  The empty set satisfies the same closure condition vacuously,
which is the degeneracy recorded by `IsLambdaOHull.empty`. -/
inductive IsLambdaOHull {P : Type uMon} [CommMonoid P] (Scaling : Set P) :
    Set P → Prop
  /-- `Set.univ` is `1 · O`. -/
  | univ : IsLambdaOHull Scaling Set.univ
  /-- A subset of the form `λ·O` with every component of `λ` nonzero. -/
  | scaled (lam : P) (hlam : lam ∈ Scaling) : IsLambdaOHull Scaling Set.univ
  /-- The empty set satisfies the same closure condition vacuously. -/
  | empty : IsLambdaOHull Scaling (∅ : Set P)

theorem isLambdaOHull_empty {P : Type uMon} [CommMonoid P] (Scaling : Set P) :
    IsLambdaOHull Scaling (∅ : Set P) :=
  IsLambdaOHull.empty

theorem isLambdaOHull_univ {P : Type uMon} [CommMonoid P] (Scaling : Set P) :
    IsLambdaOHull Scaling Set.univ :=
  IsLambdaOHull.univ

/-- The literal paper interface for the arithmetic holomorphic hull of
Remark 3.9.5, (i): the image set whose hull is taken together with the
nondegeneracy that the empty set is *not* a hull of the paper's `λ·O` form.  The
hull form itself is the concrete predicate `IsLambdaOHull` (which does contain
`∅`), so an interface demanding both is contradictory.  This is what the proof of
Corollary 3.12 needs and what `OriginalInput` does not supply. -/
structure LiteralArithmeticHullInterface (P : Type uMon) [CommMonoid P]
    (Scaling : Set P) where
  /-- The image set whose holomorphic hull is taken: the union of possible images
  of the theta-pilot object. -/
  imageSet : Set P
  /-- The image set is nonempty: the paper only takes hulls of nonempty unions of
  possible images of a theta-pilot object. -/
  imageSet_nonempty : imageSet.Nonempty
  /-- The interface excludes the empty set from the hulls of the `λ·O` form.  This
  is the nondegeneracy that the compactness/log-volume input supplies in the
  paper, and it is not a consequence of the hull form itself. -/
  not_empty_isLambdaOHull : ¬ IsLambdaOHull Scaling (∅ : Set P)

/-- Any literal hull interface that carries the paper's `λ·O` hull form and also
demands that the empty set is not such a hull is contradictory.  The mathematical
content is that the nondegeneracy is *not* part of the purely combinatorial hull
operation; it is an extra input, and in the proof of Corollary 3.12 that input is
the compactness of `1,◦U_{j,vQ}` together with the definition of the log-volume.
Hence the paper's finiteness conclusion cannot be recovered from the hull
operation alone. -/
theorem literalHullInterface_impossible {P : Type uMon} [CommMonoid P]
    (Scaling : Set P) :
    ¬ Nonempty (LiteralArithmeticHullInterface P Scaling) := by
  rintro ⟨W⟩
  exact W.not_empty_isLambdaOHull (isLambdaOHull_empty Scaling)

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT


