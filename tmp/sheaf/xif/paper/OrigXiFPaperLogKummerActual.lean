import tmp.sheaf.xif.PaperQPilotObject
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportConjugation

/-!
# OrigXiF: the actual log-Kummer arrow of the paper q-pilot object

Layer: **O** (original Theta-link route), per `coord/XI_F_ORIGINAL_ROUTE.md`.
Nothing here touches the normalized model (`NormXiF`), the native target
(`Native`), the `SourceDefinition31Data` contract, or the D4-D9 assembly.

## What is constructed

`PaperQPilotObject.logKummer` has type `SourceKummerArrow G envStrip strip`,
where `strip = sourceQPilotStrip boundary` is the `F`-layer strip of the source
input's Hodge theater.  `SourceKummerArrow` is the frozen reduced record of
`SourceKummerEvaluationArrows.lean`: its first field is one
`FPrimeStripEquiv envStrip strip` representative, its second field is a
`SourceTimesMuKummerLayer G envStrip strip` (the Definition 4.9 (i) x-mu
content: one action per place plus a `TimesMuKummer.Isomorphism` per place).

This file

* constructs that arrow from actual F-prime-strip data: a strip equivalence
  `phi : FPrimeStripEquiv envStrip strip` (its first field) together with an
  action factorization `f : forall v, G ->* envStrip.Pi v`; the layer's
  actions are the actual strip units actions `FPrimeStrip.unitsAction`
  composed with `f` (on the target side with `phi.isoPi` transported), and
  the Kummer isomorphism is the torsion-quotient transport
  `TimesMuQuotient.descent (Units.mapEquiv (phi.isoMon v))`; the equivariance
  and the invariant-image law are **proved** (`descent_action`,
  `descent_image_invariantImage`), not assumed;
* records that the arrow's first field is *exactly* the supplied `phi`
  (`OrigXiFLogKummerArrow_stripIso`, `OrigXiFPaperLogKummer_stripIso`);
* proves the inhabitation equivalence `Nonempty (SourceKummerArrow G upper
  lower) <-> Nonempty (FPrimeStripEquiv upper lower)`: the x-mu layer is not an
  independent obstruction, so the exact first field of
  `PaperQPilotObject.logKummer` is an `FPrimeStripEquiv envStrip strip`;
* plugs the constructed arrow into an existing `PaperQPilotObject`
  (`OrigXiFPaperQPilotObjectWithLogKummer`).

## What is not claimed

* The constructed Kummer isomorphism is the canonical one induced by the strip
  equivalence.  The paper's log-Kummer representation of the q-pilot on
  `1,circ U_Q` is not identified with it; that identification is the content
  of `paper_logKummer_identification`, which stays open.
* No inhabitant of the first field is produced here: this file constructs no
  general source datum supplying an actual
  `FPrimeStripEquiv envStrip (sourceQPilotStrip boundary)`, and the tree
  carries no such identification for a general `envStrip`.  It is the vertical
  coricity identification between the codomain-side `(n,o)`-level `env` strip
  and the source q-pilot strip.
* The `logKummer` field does not consume the line bundle.  Neither
  `PaperQPilotObject.lineBundle` nor the exact bad-place gap recorded in
  `S1144QvPaperQPilotObjectActual` enters this construction; the two gaps are
  independent.
* `SourceKummerArrow` is the reduced record (one strip representative, one
  `TimesMuKummer.Isomorphism` per place), not the paper's
  `F^boxplus-triangleright-x-mu`-prime-strip full poly-isomorphism.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.OrigXiF

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe ua uv upi umon ui uG uL uC

variable {V : Type uv}
variable {l : PrimeGeFive}

/-! ## 1. The Kummer isomorphism of a strip equivalence -/

/-- An action factorization of a group `G` through the local groups of the
upper strip: the datum that lets one group act on the units at every place.
It is actual data (a family of monoid homomorphisms), not a proposition, and
in the paper's setting it is the localization of the global group action. -/
abbrev OrigXiFActionFactorization (G : Type uG) [Group G]
    (upper : FPrimeStrip.{umon, uv, upi} V) : Type _ :=
  ∀ v : V, G →* upper.toDPrimeStrip.Pi v

/-- The torsion-quotient transport of a strip equivalence at one place
(`O^xmu` level of IUT II, Definition 4.9, (i)): the unit group equivalence
`Units.mapEquiv (phi.isoMon v)` descends to the quotients by the full torsion
subgroups. -/
noncomputable def OrigXiFKummerEquiv {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (v : V) :
    TimesMuQuotient ((upper.Mon v)ˣ) ≃* TimesMuQuotient ((lower.Mon v)ˣ) :=
  TimesMuQuotient.descent (Units.mapEquiv (phi.isoMon v))

/-- The action transported along the strip equivalence is the actual units
action of the lower strip, along the transported factorization. -/
theorem OrigXiFactionConj_eq_unitsAction {G : Type uG} [Group G]
    {upper lower : FPrimeStrip.{umon, uv, upi} V} (phi : FPrimeStripEquiv upper lower)
    (f : OrigXiFActionFactorization G upper) (v : V) :
    TimesMuKummer.actionConj (Units.mapEquiv (phi.isoMon v))
        ((upper.unitsAction v).comp (f v)) =
      (lower.unitsAction v).comp ((phi.isoPi v).toMonoidHom.comp (f v)) := by
  refine MonoidHom.ext (fun g => MulEquiv.ext (fun w => Units.ext ?_))
  rw [TimesMuKummer.actionConj_apply]
  simp only [MonoidHom.comp_apply, Units.coe_mapEquiv,
    FPrimeStrip.unitsAction_val]
  rw [phi.compatAction v ((f v) g)
    ((↑((Units.mapEquiv (phi.isoMon v)).symm w) : upper.Mon v))]
  rw [← Units.coe_mapEquiv (phi.isoMon v)
    ((Units.mapEquiv (phi.isoMon v)).symm w)]
  rw [MulEquiv.apply_symm_apply]; rfl

/-- The actual `TimesMuKummer.Isomorphism` at one place: the unit-group
transport `OrigXiFKummerEquiv` is equivariant for the actual strip units
actions and maps the Definition 4.9 (i) invariant submodules onto each other.
Both laws are proved from the strip equivalence. -/
noncomputable def OrigXiFKummerIsomorphism {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper)
    (v : V) :
    TimesMuKummer.Isomorphism
      ((upper.unitsAction v).comp (f v))
      ((lower.unitsAction v).comp ((phi.isoPi v).toMonoidHom.comp (f v))) where
  equiv := OrigXiFKummerEquiv phi v
  equivariant := by
    intro g x
    rw [← OrigXiFactionConj_eq_unitsAction phi f v]
    exact TimesMuQuotient.descent_action (Units.mapEquiv (phi.isoMon v))
      ((upper.unitsAction v).comp (f v)) g x
  invariantImage := by
    intro H
    rw [← OrigXiFactionConj_eq_unitsAction phi f v]
    exact TimesMuKummer.descent_image_invariantImage
      (Units.mapEquiv (phi.isoMon v)) ((upper.unitsAction v).comp (f v)) H

/-- The actual reduced x-mu Kummer layer (Card LK) of a strip equivalence:
the actual units actions of the two strips, and the per-place Kummer
isomorphisms built from the equivalence. -/
noncomputable def OrigXiFKummerLayer {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper) :
    SourceTimesMuKummerLayer G upper lower where
  sourceAction := fun v => (upper.unitsAction v).comp (f v)
  targetAction := fun v =>
    (lower.unitsAction v).comp ((phi.isoPi v).toMonoidHom.comp (f v))
  kummer := fun v => OrigXiFKummerIsomorphism phi f v

@[simp] theorem OrigXiFKummerLayer_sourceAction {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper)
    (v : V) :
    (OrigXiFKummerLayer phi f).sourceAction v = (upper.unitsAction v).comp (f v) :=
  rfl

@[simp] theorem OrigXiFKummerLayer_targetAction {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper)
    (v : V) :
    (OrigXiFKummerLayer phi f).targetAction v =
      (lower.unitsAction v).comp ((phi.isoPi v).toMonoidHom.comp (f v)) :=
  rfl

@[simp] theorem OrigXiFKummerLayer_kummer_equiv {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper)
    (v : V) :
    ((OrigXiFKummerLayer phi f).kummer v).equiv = OrigXiFKummerEquiv phi v :=
  rfl

/-! ## 2. The actual log-Kummer arrow and its first field -/

/-- The actual reduced log-Kummer arrow `upper -> lower` of a strip
equivalence: the first field is `phi` itself, the second is the actual x-mu
layer of Section 1. -/
noncomputable def OrigXiFLogKummerArrow {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper) :
    SourceKummerArrow G upper lower :=
  sourceKummerArrowOfLayer phi (OrigXiFKummerLayer phi f)

/-- The first field of the constructed arrow is exactly the supplied strip
equivalence. -/
@[simp] theorem OrigXiFLogKummerArrow_stripIso {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper) :
    (OrigXiFLogKummerArrow phi f).stripIso = phi :=
  rfl

/-- The second field of the constructed arrow is exactly the constructed x-mu
layer. -/
@[simp] theorem OrigXiFLogKummerArrow_layer {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (phi : FPrimeStripEquiv upper lower) (f : OrigXiFActionFactorization G upper) :
    (OrigXiFLogKummerArrow phi f).layer = OrigXiFKummerLayer phi f :=
  rfl

/-- Inhabitation characterization (gate): the reduced Kummer arrow is
inhabited exactly when its **first field** is.  The x-mu layer is never an
independent obstruction, since Section 1 builds it from the first field (the
converse below uses the trivial factorization, which exists for every group).
This is a satisfiability statement, not the paper's Kummer isomorphism. -/
theorem OrigXiFLogKummerArrow_nonempty_iff {G : Type uG} [Group G]
    [TopologicalSpace G] (upper lower : FPrimeStrip.{umon, uv, upi} V) :
    Nonempty (SourceKummerArrow G upper lower) ↔
      Nonempty (FPrimeStripEquiv upper lower) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.stripIso⟩
  · rintro ⟨phi⟩
    have f : OrigXiFActionFactorization G upper := fun _ => 1
    exact ⟨OrigXiFLogKummerArrow (upper := upper) (lower := lower) phi f⟩

/-! ## 3. The `PaperQPilotObject.logKummer` slot -/

variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The exact first field of `PaperQPilotObject.logKummer` for a source
boundary and a strip `envStrip`: the strip equivalence from the environment
strip to the source q-pilot strip.  No inhabitant is produced here. -/
abbrev OrigXiFPaperLogKummerFirstField
    (boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (envStrip : FPrimeStrip.{umon, uv, upi} V) :=
  FPrimeStripEquiv envStrip (sourceQPilotStrip boundary)

/-- The exact remaining obligation for `PaperQPilotObject.logKummer`: an
actual strip equivalence between the environment strip and the source q-pilot
strip, with no other data.  This is a definition of the obligation's type, not
a proof of it. -/
abbrev OrigXiFPaperLogKummerExact
    (boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (envStrip : FPrimeStrip.{umon, uv, upi} V) : Prop :=
  Nonempty (OrigXiFPaperLogKummerFirstField (l := l) (V := V)
    (Label := Label) (Choice := Choice) boundary envStrip)

/-- The actual `logKummer` field of the paper q-pilot object, constructed from
the strip equivalence and the action factorization. -/
noncomputable def OrigXiFPaperLogKummer {G : Type uG} [Group G]
    [TopologicalSpace G] {envStrip : FPrimeStrip.{umon, uv, upi} V}
    (boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (phi : OrigXiFPaperLogKummerFirstField (l := l) (V := V)
      (Label := Label) (Choice := Choice) boundary envStrip)
    (f : OrigXiFActionFactorization G envStrip) :
    SourceKummerArrow G envStrip (sourceQPilotStrip boundary) :=
  OrigXiFLogKummerArrow phi f

/-- The constructed paper log-Kummer arrow's first field is exactly the
supplied strip equivalence. -/
@[simp] theorem OrigXiFPaperLogKummer_stripIso {G : Type uG} [Group G]
    [TopologicalSpace G] {envStrip : FPrimeStrip.{umon, uv, upi} V}
    (boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (phi : OrigXiFPaperLogKummerFirstField (l := l) (V := V)
      (Label := Label) (Choice := Choice) boundary envStrip)
    (f : OrigXiFActionFactorization G envStrip) :
    (OrigXiFPaperLogKummer boundary phi f).stripIso = phi :=
  rfl

/-- **The exact first field.**  For any source boundary and any environment
strip, the `logKummer` field is inhabited exactly when the first field is: the
Kummer layer adds no obstruction.  Since the source data supplies no actual
strip equivalence `envStrip ~ sourceQPilotStrip boundary`, this is the
remaining gap of the field (the vertical coricity identification), not a
Kummer-theoretic one. -/
theorem OrigXiFPaperLogKummer_nonempty_iff_exact {G : Type uG} [Group G]
    [TopologicalSpace G] {envStrip : FPrimeStrip.{umon, uv, upi} V}
    (boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
      (l := l) (V := V) (Label := Label) (Choice := Choice)) :
    Nonempty (SourceKummerArrow G envStrip (sourceQPilotStrip boundary)) ↔
      OrigXiFPaperLogKummerExact (l := l) (V := V) (Label := Label)
        (Choice := Choice) boundary envStrip := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.stripIso⟩
  · rintro ⟨phi⟩
    have f : OrigXiFActionFactorization G envStrip := fun _ => 1
    exact ⟨OrigXiFPaperLogKummer boundary phi f⟩

/-- Any actual `PaperQPilotObject` already carries an actual strip equivalence
`envStrip ~ strip` as the first field of its `logKummer`.  Hence the first
field is genuinely present in the paper object surface.  The separate
obligation `paper_logKummer_identification` (identifying the reduced arrow with
the paper's log-Kummer representation) is untouched by this observation. -/
theorem OrigXiFPaperQPilotObject_logKummer_firstField {G : Type uG} [Group G]
    [TopologicalSpace G] {envStrip : FPrimeStrip.{umon, uv, upi} V}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    Nonempty (FPrimeStripEquiv envStrip O.strip) :=
  ⟨O.logKummer.stripIso⟩

/-- Replace the `logKummer` field of an existing paper q-pilot object by the
actual arrow of Section 1, from the strip equivalence and the action
factorization.  Every other field (boundary, strip, one-column structure, line
bundle, q-pilot log-volume, and the four identification props) is untouched. -/
noncomputable def OrigXiFPaperQPilotObjectWithLogKummer {G : Type uG} [Group G]
    [TopologicalSpace G] {envStrip : FPrimeStrip.{umon, uv, upi} V}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (phi : FPrimeStripEquiv envStrip O.strip)
    (f : OrigXiFActionFactorization G envStrip) :
    PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip :=
  { O with logKummer := OrigXiFLogKummerArrow phi f }

/-- The replaced object's `logKummer` is the constructed actual arrow. -/
@[simp] theorem OrigXiFPaperQPilotObjectWithLogKummer_logKummer {G : Type uG}
    [Group G] [TopologicalSpace G] {envStrip : FPrimeStrip.{umon, uv, upi} V}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (phi : FPrimeStripEquiv envStrip O.strip)
    (f : OrigXiFActionFactorization G envStrip) :
    (OrigXiFPaperQPilotObjectWithLogKummer O phi f).logKummer =
      OrigXiFLogKummerArrow phi f :=
  rfl

/-- The replaced object's log-Kummer arrow has the supplied strip equivalence
as its first field. -/
@[simp] theorem OrigXiFPaperQPilotObjectWithLogKummer_stripIso {G : Type uG}
    [Group G] [TopologicalSpace G] {envStrip : FPrimeStrip.{umon, uv, upi} V}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (phi : FPrimeStripEquiv envStrip O.strip)
    (f : OrigXiFActionFactorization G envStrip) :
    (OrigXiFPaperQPilotObjectWithLogKummer O phi f).logKummer.stripIso = phi :=
  rfl

/-! ## 4. Interface checks -/

#check @OrigXiFKummerIsomorphism
#check @OrigXiFKummerLayer
#check @OrigXiFLogKummerArrow
#check @OrigXiFLogKummerArrow_stripIso
#check @OrigXiFLogKummerArrow_nonempty_iff
#check @OrigXiFPaperLogKummerFirstField
#check @OrigXiFPaperLogKummer
#check @OrigXiFPaperLogKummer_nonempty_iff_exact
#check @OrigXiFPaperQPilotObjectWithLogKummer

end LeanFormal.IUT.XiFPaper.OrigXiF
