import Mathlib.Tactic
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import tmp.sheaf.xif.PaperQPilotObject

/-! # Layer O: actual `SourceProcessionBoundary.Input` and `sourceQPilotStrip`

Layer: **O** (original-text Theta-link).  This file constructs only the
`boundary` / `strip` / `strip_eq_source` slots of
`Theorem311Source.PaperQPilotObject` from the paper original input
`I : OriginalInput l V`; it does not use the normalized model (N), the native
target (T), the `SourceDefinition31Data` contract as a target (S), or any
D4-D9 assembly (D).

## What is actual here

For every original input `I : OriginalInput l V` the actual source family gives

* `OrigXiFPaperCore`: the `ParametricTheorem311.Core` on the actual family
  index together with the vertical level coordinate, with
  `ind1 g (i,k) = (I.translate g.1 0 i, k)`,
  `ind2 g (i,k) = (I.translate 0 g.2 i, k)`,
  `ind3 n (i,k) = (i, k + n)`, `level (i,k) = k`;
* `OrigXiFPaperProfile`: the actual theater log-volume
  `(I.family.theater i).thetaPacket.logVolume`, constant on the family index
  because the family links preserve the theta q (proved here from
  `FiniteThetaPacket.log_scale` and `I.family.link_q`), with the singleton
  possible image;
* `OrigXiFPaperCarrier`: the source procession carrier whose connector moves
  along the two actual lattice translations and whose `ind3_level_eq` is the
  level coordinate;
* `OrigXiFPaperBoundary`: the actual `SourceProcessionBoundary.Input` whose
  theater is `I.theaterAt n m`, whose history is the reflexive singleton
  history of that theater, and whose packet volume at the base choice is the
  actual theta log-volume (proved, not assumed);
* `OrigXiFPaperStrip`: `sourceQPilotStrip (OrigXiFPaperBoundary I n m)`, i.e.
  the actual `F`-prime-strip of the input theater (the anchor's own
  definition, no identification asserted).

`OrigXiFPaperBoundaryStripFields` records exactly the three `PaperQPilotObject`
fields `boundary`, `strip`, `strip_eq_source`; `ofPaperQPilotObject` shows
that every `PaperQPilotObject` restricts to it, and
`OrigXiFPaperBoundaryStripActual` is the actual inhabitant at
`Label := ℤ × ℤ`, `Choice := I.family.index × ℕ`.

## What is NOT claimed

* The strip is only the input Hodge theater's `F`-layer strip; it is **not**
  identified with the paper's q-pilot `F^boxplus-triangleright-x-mu`-prime-strip
  (`PaperQPilotObject.paper_strip_identification` is untouched here).
* No `PaperQPilotObject` inhabitant is asserted; the file supplies only its
  boundary/strip slots.

## Exact remaining datum at a user-chosen `Choice`

`PaperQPilotObject` is polymorphic in `Label` and `Choice` with only
`[AddGroup Label] [Preorder Choice]`.  Neither `OriginalInput` nor the
boundary module constructs a procession carrier for such an arbitrary pair:
the first missing field of the boundary is a value of
`ParametricTheorem311.Carrier Label Choice` (whose `ind3_level_eq` requires an
actual `ℕ`-valued level that `OriginalInput` does not carry), together with an
inhabitant of `Choice` for `baseChoice`.  This file therefore supplies the
carrier from the actual source family index plus the level coordinate (the
`(n,m) × level` shape of the concrete finite source choice), and records the
generic case as the exact missing `Carrier` datum in the module documentation
rather than fabricating one.

No `True`, `PUnit`, empty type, `sorry`, `axiom`, arbitrary inhabitant or
`Nonempty` gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.OrigXiFPaperBoundaryStrip

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel

universe ua uv upi umon ui uG uL uC

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Label and choice types from the actual source family -/

/-- The label type of the constructed source procession: the actual lattice
coordinates `(n,m)` of the original input. -/
abbrev OrigXiFPaperLabel : Type := ℤ × ℤ

/-- The choice type of the constructed source procession: the actual family
index together with the vertical level coordinate.  This is the
`(n,m) × level` shape of the concrete finite source choice, built from the
input's own family index. -/
abbrev OrigXiFPaperChoice (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Type ui :=
  I.family.index × ℕ

/-- The source base choice: the `(1,0)` lattice point at level zero. -/
abbrev OrigXiFPaperBase (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    OrigXiFPaperChoice I :=
  (I.indexOf 0 0, 0)

/-- The coordinate representative of a family index. -/
theorem OrigXiFPaperIndexOfIndexEquiv
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (i : I.family.index) :
    I.indexOf (I.index_equiv i).1 (I.index_equiv i).2 = i := by
  exact Equiv.symm_apply_apply I.index_equiv i

/-! ## 2. The actual core on the source family index -/

/-- The actual `Core` of the source procession.  The two horizontal operations
are the actual lattice translations of the original input, and `ind3` is the
vertical shift of the level coordinate. -/
noncomputable def OrigXiFPaperCore
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Core OrigXiFPaperLabel (OrigXiFPaperChoice I) where
  base := OrigXiFPaperBase I
  level c := c.2
  ind1 g c := (I.translate g.1 0 c.1, c.2)
  ind2 g c := (I.translate 0 g.2 c.1, c.2)
  ind3 n c := (c.1, c.2 + n)
  ind1_zero := by
    intro c
    apply Prod.ext
    · exact I.translate_zero c.1
    · rfl
  ind1_add := by
    intro g h c
    apply Prod.ext
    · show I.translate (g + h).1 0 c.1 = I.translate h.1 0 (I.translate g.1 0 c.1)
      rw [I.translate_add]
      rfl
    · rfl
  ind1_inverse := by
    intro g c
    apply Prod.ext
    · show I.translate (-g).1 0 (I.translate g.1 0 c.1) = c.1
      rw [I.translate_add]
      have hneg : (-g).1 = -g.1 := rfl
      rw [hneg, show g.1 + -g.1 = 0 by ring]
      simpa using I.translate_zero c.1
    · rfl
  ind2_zero := by
    intro c
    apply Prod.ext
    · exact I.translate_zero c.1
    · rfl
  ind2_add := by
    intro g h c
    apply Prod.ext
    · show I.translate 0 (g + h).2 c.1 = I.translate 0 h.2 (I.translate 0 g.2 c.1)
      rw [I.translate_add]
      rfl
    · rfl
  ind2_inverse := by
    intro g c
    apply Prod.ext
    · show I.translate 0 (-g).2 (I.translate 0 g.2 c.1) = c.1
      rw [I.translate_add]
      have hneg : (-g).2 = -g.2 := rfl
      rw [hneg, show g.2 + -g.2 = 0 by ring]
      simpa using I.translate_zero c.1
    · rfl
  ind3_zero := by
    intro c
    apply Prod.ext
    · rfl
    · simp
  ind3_add := by
    intro m n c
    apply Prod.ext
    · rfl
    · omega
  ind1_ind2_commute := by
    intro g h c
    apply Prod.ext
    · exact I.translate_commute g.1 0 0 h.2 c.1
    · rfl
  ind1_ind3_commute := by
    intro g n c
    rfl
  ind2_ind3_commute := by
    intro g n c
    rfl
  ind1_level := by
    intro g c
    rfl
  ind2_level := by
    intro g c
    rfl
  ind3_level := by
    intro n c
    omega

/-! ## 3. The actual source log-volume and profile -/

/-- The actual theater theta log-volume attached to a source choice. -/
noncomputable def OrigXiFPaperLogVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : OrigXiFPaperChoice I) : Real :=
  (I.family.theater c.1).thetaPacket.logVolume

/-- The actual theater theta log-volume is constant on the source family index:
the family links preserve the theta q, and `FiniteThetaPacket.logVolume` is
determined by q through the Gaussian exponents. -/
theorem OrigXiFPaperThetaLogVolume_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (i j : I.family.index) :
    (I.family.theater i).thetaPacket.logVolume =
      (I.family.theater j).thetaPacket.logVolume := by
  rw [FiniteThetaPacket.logVolume_eq_sum, FiniteThetaPacket.logVolume_eq_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [FiniteThetaPacket.log_scale, FiniteThetaPacket.log_scale, I.family.link_q i j]

/-- Constancy of the source log-volume on choices. -/
theorem OrigXiFPaperLogVolume_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c c' : OrigXiFPaperChoice I) :
    OrigXiFPaperLogVolume I c = OrigXiFPaperLogVolume I c' :=
  OrigXiFPaperThetaLogVolume_eq I c.1 c'.1

/-- The actual `Profile` of the source procession: the actual theater
log-volume with the singleton possible image. -/
noncomputable def OrigXiFPaperProfile
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Profile (OrigXiFPaperCore I) where
  logVolume := OrigXiFPaperLogVolume I
  possibleImage c := {OrigXiFPaperLogVolume I c}
  ind1_invariant := by
    intro g c
    exact OrigXiFPaperLogVolume_eq I ((OrigXiFPaperCore I).ind1 g c) c
  ind2_invariant := by
    intro g c
    exact OrigXiFPaperLogVolume_eq I ((OrigXiFPaperCore I).ind2 g c) c
  ind3_upper := by
    intro n c
    exact le_of_eq (OrigXiFPaperLogVolume_eq I c ((OrigXiFPaperCore I).ind3 n c))
  possibleImage_nonempty := by
    intro c
    exact ⟨OrigXiFPaperLogVolume I c, by simp⟩
  possibleImage_ind1 := by
    intro g c
    rw [OrigXiFPaperLogVolume_eq I ((OrigXiFPaperCore I).ind1 g c) c]
  possibleImage_ind2 := by
    intro g c
    rw [OrigXiFPaperLogVolume_eq I ((OrigXiFPaperCore I).ind2 g c) c]
  possibleImage_ind3 := by
    intro n c z hz
    refine ⟨OrigXiFPaperLogVolume I ((OrigXiFPaperCore I).ind3 n c), by simp, ?_⟩
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact le_of_eq (OrigXiFPaperLogVolume_eq I c ((OrigXiFPaperCore I).ind3 n c))

/-! ## 4. The actual source procession carrier -/

/-- The connector between two source choices: the two actual lattice
translations to the target `(n,m)` coordinates.  Both steps are horizontal. -/
noncomputable def OrigXiFPaperConnector
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (a b : OrigXiFPaperChoice I) : List (RouteStep OrigXiFPaperLabel) :=
  [RouteStep.ind1 ((I.index_equiv b.1).1 - (I.index_equiv a.1).1),
   RouteStep.ind2 ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)]

/-- Every step of the source connector is horizontal. -/
theorem OrigXiFPaperConnector_horizontal
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (a b : OrigXiFPaperChoice I) :
    ∀ step ∈ OrigXiFPaperConnector I a b, horizontal step := by
  intro step hstep
  simp [OrigXiFPaperConnector] at hstep
  rcases hstep with rfl | rfl
  · exact horizontal_of_ind1 _
  · exact horizontal_of_ind2 _

/-- The source connector reaches the target choice at equal level. -/
theorem OrigXiFPaperConnector_apply
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (a b : OrigXiFPaperChoice I)
    (hlevel : (OrigXiFPaperCore I).level a = (OrigXiFPaperCore I).level b) :
    applyRoute (OrigXiFPaperCore I) (OrigXiFPaperConnector I a b) a = b := by
  change (I.translate 0 ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)
      (I.translate ((I.index_equiv b.1).1 - (I.index_equiv a.1).1) 0 a.1), a.2) = b
  apply Prod.ext
  · rw [I.translate_add]
    simp only [add_zero, zero_add]
    calc
      I.translate ((I.index_equiv b.1).1 - (I.index_equiv a.1).1)
          ((I.index_equiv b.1).2 - (I.index_equiv a.1).2) a.1
          = I.translate ((I.index_equiv b.1).1 - (I.index_equiv a.1).1)
              ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)
              (I.indexOf (I.index_equiv a.1).1 (I.index_equiv a.1).2) := by
            rw [OrigXiFPaperIndexOfIndexEquiv]
      _ = I.indexOf
            ((I.index_equiv a.1).1 + ((I.index_equiv b.1).1 - (I.index_equiv a.1).1))
            ((I.index_equiv a.1).2 + ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)) :=
            I.translate_theater _ _ _ _
      _ = I.indexOf (I.index_equiv b.1).1 (I.index_equiv b.1).2 := by
            rw [show (I.index_equiv a.1).1 +
                  ((I.index_equiv b.1).1 - (I.index_equiv a.1).1) =
                  (I.index_equiv b.1).1 by ring,
                show (I.index_equiv a.1).2 +
                  ((I.index_equiv b.1).2 - (I.index_equiv a.1).2) =
                  (I.index_equiv b.1).2 by ring]
      _ = b.1 := OrigXiFPaperIndexOfIndexEquiv I b.1
  · exact hlevel

/-- The actual source procession carrier. -/
noncomputable def OrigXiFPaperCarrier
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    ParametricTheorem311.Carrier OrigXiFPaperLabel (OrigXiFPaperChoice I) where
  core := OrigXiFPaperCore I
  profile := OrigXiFPaperProfile I
  connector := OrigXiFPaperConnector I
  connector_horizontal := fun a b => OrigXiFPaperConnector_horizontal I a b
  connector_target_same_level := by
    intro a b hlevel
    exact OrigXiFPaperConnector_apply I a b hlevel
  ind3_level_eq := by
    intro n c
    rfl

/-! ## 5. The actual source procession boundary and its strip -/

/-- The actual `SourceProcessionBoundary.Input` built from the original input:
the theater at `(n,m)`, its reflexive singleton history, the actual source
carrier, and the actual theater theta log-volume at the base choice. -/
noncomputable def OrigXiFPaperBoundary
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    SourceProcessionBoundary.Input.{ua, uv, upi, umon, 0, ui}
      (l := l) (V := V) (Label := OrigXiFPaperLabel) (Choice := OrigXiFPaperChoice I) where
  theater := I.theaterAt n m
  history := HodgeTheaterHistory.singleton (I.theaterAt n m)
  carrier := OrigXiFPaperCarrier I
  baseChoice := OrigXiFPaperBase I
  baseChoice_eq := rfl
  packetVolume := fun c => (OrigXiFPaperCarrier I).profile.logVolume c
  packetVolume_eq_profile := by
    intro c
    rfl
  base_packetVolume_eq_theta := by
    show OrigXiFPaperLogVolume I (OrigXiFPaperBase I) =
      (I.theaterAt n m).thetaPacket.logVolume
    exact OrigXiFPaperLogVolume_eq I (OrigXiFPaperBase I) (I.indexOf n m, 0)
  target_q := (I.theaterAt n m).thetaPacket.q
  target_q_eq := rfl
  history_q_eq := rfl
  route_normal_form := by
    intro route
    refine ⟨((ParametricTheorem311.routeTarget (OrigXiFPaperCarrier I) route
        (OrigXiFPaperBase I)).1, 0),
      ParametricTheorem311.verticalBudget route, ?_, ?_⟩
    · rfl
    · apply Prod.ext
      · rfl
      · have h := ParametricTheorem311.routeTarget_level_eq_budget
            (OrigXiFPaperCarrier I) route (OrigXiFPaperBase I)
        simpa [OrigXiFPaperCarrier, OrigXiFPaperCore, OrigXiFPaperBase] using h

/-- The actual paper q-pilot strip anchor: the source q-pilot strip of the
actual boundary, i.e. the input theater's `F`-prime-strip. -/
noncomputable def OrigXiFPaperStrip
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    FPrimeStrip.{umon, uv, upi} V :=
  sourceQPilotStrip (OrigXiFPaperBoundary I n m)

/-- The strip is definitionally the source q-pilot strip of the actual
boundary. -/
@[simp] theorem OrigXiFPaperStrip_eq_source
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    OrigXiFPaperStrip I n m = sourceQPilotStrip (OrigXiFPaperBoundary I n m) := rfl

/-- The strip is the actual `F`-prime-strip of the input theater. -/
@[simp] theorem OrigXiFPaperStrip_eq_theater
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    OrigXiFPaperStrip I n m = (I.theaterAt n m).primeStrip := rfl

/-! ## 6. The boundary/strip slots of `PaperQPilotObject` -/

/-- Exactly the three `PaperQPilotObject` fields `boundary`, `strip`,
`strip_eq_source`; the paper identification fields are not part of this
package. -/
structure OrigXiFPaperBoundaryStripFields
    (l : PrimeGeFive) (V : Type uv) (Label : Type uL) (Choice : Type uC) [AddGroup Label] where
  /-- The actual source procession boundary. -/
  boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
    (l := l) (V := V) (Label := Label) (Choice := Choice)
  /-- The actual `F`-layer source strip anchor. -/
  strip : FPrimeStrip.{umon, uv, upi} V
  /-- The actual source strip of the boundary. -/
  strip_eq_source : strip = sourceQPilotStrip boundary

/-- The actual inhabitant of the boundary/strip package at
`Label := ℤ × ℤ`, `Choice := I.family.index × ℕ`. -/
noncomputable def OrigXiFPaperBoundaryStripActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    OrigXiFPaperBoundaryStripFields (l := l) (V := V)
      (Label := OrigXiFPaperLabel) (Choice := OrigXiFPaperChoice I) where
  boundary := OrigXiFPaperBoundary I n m
  strip := OrigXiFPaperStrip I n m
  strip_eq_source := rfl

/-- Every `PaperQPilotObject` restricts to the boundary/strip package: its
`boundary`, `strip` and `strip_eq_source` fields have exactly these types. -/
noncomputable def OrigXiFPaperBoundaryStripFields.ofPaperQPilotObject
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip.{umon, uv, upi} V}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip) :
    OrigXiFPaperBoundaryStripFields (l := l) (V := V) (Label := Label) (Choice := Choice) where
  boundary := O.boundary
  strip := O.strip
  strip_eq_source := O.strip_eq_source

/-! ## 7. Projections -/

@[simp] theorem OrigXiFPaperBoundaryStripActual_boundary
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (OrigXiFPaperBoundaryStripActual I n m).boundary = OrigXiFPaperBoundary I n m := rfl

@[simp] theorem OrigXiFPaperBoundaryStripActual_strip
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (OrigXiFPaperBoundaryStripActual I n m).strip = OrigXiFPaperStrip I n m := rfl

@[simp] theorem OrigXiFPaperBoundary_theater
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (OrigXiFPaperBoundary I n m).theater = I.theaterAt n m := rfl

@[simp] theorem OrigXiFPaperBoundary_baseChoice
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (OrigXiFPaperBoundary I n m).baseChoice = OrigXiFPaperBase I := rfl

@[simp] theorem OrigXiFPaperBoundary_target_q
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (OrigXiFPaperBoundary I n m).target_q = (I.theaterAt n m).thetaPacket.q := rfl

/-- The base packet volume of the actual boundary is the actual theta
log-volume of its theater. -/
theorem OrigXiFPaperBoundary_baseVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (OrigXiFPaperBoundary I n m).packetVolume (OrigXiFPaperBase I) =
      (I.theaterAt n m).thetaPacket.logVolume :=
  (OrigXiFPaperBoundary I n m).base_packetVolume_eq_theta

/-- The route normal form of the actual boundary holds for every route. -/
theorem OrigXiFPaperBoundary_route_normal_form
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep OrigXiFPaperLabel)) :
    ∃ b nc,
      (OrigXiFPaperBoundary I n m).carrier.core.level b =
          (OrigXiFPaperBoundary I n m).carrier.core.level
            (OrigXiFPaperBoundary I n m).carrier.core.base ∧
      ParametricTheorem311.routeTarget (OrigXiFPaperBoundary I n m).carrier route
          (OrigXiFPaperBoundary I n m).carrier.core.base =
        (OrigXiFPaperBoundary I n m).carrier.core.ind3 nc b :=
  (OrigXiFPaperBoundary I n m).route_normal_form route

end LeanFormal.IUT.XiFPaper.OrigXiFPaperBoundaryStrip

end
