import tmp.sheaf.xif.SourceXiFConstruction
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Value-layer surrogate: Theta-hull signed log-volume nonpositivity and finite phase

**VALUE-LAYER SURROGATE — NOT PAPER XI-F.** This file works only at the actual
source *value layer* of `SourceXiFConstruction.lean`. It does not construct the
paper's q-pilot object, the signed `1,circ U_{j,vQ}` hull, the O-module/vector-
bundle layer, or the paper xi-f inclusion. `target_accepted=false`; these results
must not be substituted for the new paper-level tasks.

Recall the objects from that file:

* `sourceQPilotPoint`: the theta-pilot point at signed label `j = 1`;
* `sourceQPilotLogVolume`: its actual source local log-degree;
* `sourceThetaHullLogValueSet`: the image of the actual source holomorphic hull
  under the actual source local log-degree;
* `sourceThetaHullLogVolume := sSup sourceThetaHullLogValueSet`.

The main results here:

* the hull log-value set is nonempty;
* under the actual contracted-generator hypotheses (`q <= 1` and every hull
  scaling has nonpositive log-degree), the hull log-value set is bounded above by
  `0`, and `sourceThetaHullLogVolume <= 0`;
* at `q = 1` the hull log-volume is exactly `0`;
* the actual source hull Haar volume is finite and is bounded by the actual
  source possible-image/edge volume under the same contraction hypotheses.

## What `-|log Theta|` still requires

`sourceThetaHullLogVolume` is the supremum of the actual local log-degrees on
the value-layer hull. It is **not** by itself the paper's procession-normalized
mono-analytic log-volume `-|log Theta|`. The paper object additionally requires
(i) the compact `1,circ U_{j,vQ}`/IQ-carrier hull, (ii) the procession average
over `j in F_l^*`, and (iii) the log-shell/Haar log-volume normalization
`mu(O)=1` together with the determinant/log-volume comparison. None of those is
an equality theorem in the present source declarations. What is proved here is
the nonpositive signed value (`sourceThetaHullLogVolume <= 0`) and the finite
Haar phase (`sourceHullVolume < top`), together with the actual hull <= image
comparison; the exact equality with `-|log Theta|` remains an interface
obligation, not an asserted identity.

## Exact object/statement mismatches with paper xi-f

The following are deliberate limitations, not paper-level identifications:

1. **q-pilot object.** `sourceQPilotPoint` is the theta-pilot point at the signed
   label `j = 1`; it is not the paper q-pilot object at `(1,0)`.
2. **q-pilot log-volume.** `sourceQPilotLogVolume` equals
   `card(SourceVolumeIndex l) * log(q)` for that label
   (`sourceQPilotLogVolume_eq_gauss`); at `l = 41` this is `861 * log(q)`, not
   the paper's `-|log q|`. The signed q-pilot normalization is absent.
3. **Theta-hull log-volume.** `sourceThetaHullLogVolume` is the supremum of the
   pointwise local log-degrees over the value-layer holomorphic hull; it is not
   the paper's procession-normalized mono-analytic log-volume of the
   `1,circ U_{j,vQ}` hull. The procession average over `j in F_l^*` and the
   log-shell/Haar normalization are not part of this definition.
4. **Haar-volume comparison.** `sourceHullVolume`/`sourceImageVolume` are
   `ENNReal` Haar/edge volumes of the value layer, not the signed
   log-volumes; the inequality `sourceHullVolume <= sourceImageVolume` proved
   below is not an identification of `-|log Theta|` with a signed volume.
   Under `hq`/`hScaling` this value-layer hull Haar volume is in fact `0`
   (`sourceHullVolume_eq_zero_of_q_le_one_and_scaling`); it is a degenerate
   finite phase, not the paper's positive finite normalized hull volume.
5. **Substantive hypotheses.** `hq : q <= 1` and
   `hScaling : every source hull scaling has nonpositive log-degree` are real
   extra hypotheses. Under `OriginalInput` alone the hull is unbounded (the
   import notes `sourceHolomorphicHull_logDegree_unbounded`), so this file is a
   sufficient contraction regime, not an unconditional source theorem.
6. **No paper compactness.** The compactness of `1,circ U_{j,vQ}` and the
   paper's log-volume normalization are not formalized here; they are exactly
   what a paper-level `-|log Theta|` construction must add.

Accordingly, the theorem names below are value-layer facts conditional on
`hq`/`hScaling`; they are not a substitute for the paper-level q-pilot,
signed-hull, O-module/vector-bundle, or inclusion tasks.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual hull log-value set is nonempty: the q-pilot point lies in the
source holomorphic hull and contributes its actual local log-degree. -/
theorem sourceThetaHullLogValueSet_nonempty (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.sourceThetaHullLogValueSet v R n).Nonempty :=
  ⟨I.sourceQPilotLogVolume v R n,
    I.sourceQPilotLogVolume_mem_valueSet v R n⟩

/-- General real-sup upper bound for the hull log-volume: if every hull value is
at most `B`, then its supremum is at most `B`. -/
theorem sourceThetaHullLogVolume_le_of_forall_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {B : Real}
    (hB : ∀ x, x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      I.sourceLocalLogDegree v x ≤ B) :
    I.sourceThetaHullLogVolume v R n ≤ B := by
  unfold sourceThetaHullLogVolume
  refine csSup_le (I.sourceThetaHullLogValueSet_nonempty v R n) ?_
  rintro y ⟨x, hx, rfl⟩
  exact hB x hx

/-- Exact real-sup lemma: if `B` is an upper bound of all hull log-degrees and
`B` itself occurs as a hull value, then the hull signed log-volume is exactly
`B`. -/
theorem sourceThetaHullLogVolume_eq_of_forall_le_and_mem (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {B : Real}
    (hB : ∀ x, x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      I.sourceLocalLogDegree v x ≤ B)
    (hM : B ∈ I.sourceThetaHullLogValueSet v R n) :
    I.sourceThetaHullLogVolume v R n = B := by
  have hbdd : BddAbove (I.sourceThetaHullLogValueSet v R n) := by
    refine ⟨B, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hB x hx
  apply le_antisymm (I.sourceThetaHullLogVolume_le_of_forall_le v R n hB)
  unfold sourceThetaHullLogVolume
  exact le_csSup hbdd hM

/-- Under the actual contracted-generator hypotheses (`q <= 1`; every source hull
scaling has nonpositive log-degree), the source Theta-hull signed log-volume is
nonpositive. This is the value-layer form of the paper's `-|log Theta| < 0`
nonpositivity statement. -/
theorem sourceThetaHullLogVolume_nonpos_of_contracted (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceThetaHullLogVolume v R n ≤ 0 :=
  I.sourceThetaHullLogVolume_le_of_forall_le v R n (B := 0) (by
    intro x hx
    exact I.sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators
      v R n (I.sourceImageLogDegree_nonpos_of_q_le_one v R n hq)
      hScaling x hx)

/-- At `q = 1` the hull log-volume is exactly `0`: the q-pilot value is `0` and
the contracted hull values are all nonpositive. -/
theorem sourceThetaHullLogVolume_eq_zero_of_q_eq_one (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q = 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceThetaHullLogVolume v R n = 0 := by
  have hle : I.sourceThetaHullLogVolume v R n ≤ 0 :=
    I.sourceThetaHullLogVolume_nonpos_of_contracted v R n hq.le hScaling
  have hqp : I.sourceQPilotLogVolume v R n = 0 := by
    rw [I.sourceQPilotLogVolume_eq_gauss v R n, hq, Real.log_one]
    ring
  have hbdd : BddAbove (I.sourceThetaHullLogValueSet v R n) :=
    I.sourceThetaHullLogValueSet_bddAbove_of_contracted v R n hq.le hScaling
  have hge : 0 ≤ I.sourceThetaHullLogVolume v R n := by
    unfold sourceThetaHullLogVolume
    calc
      0 = I.sourceQPilotLogVolume v R n := hqp.symm
      _ ≤ sSup (I.sourceThetaHullLogValueSet v R n) :=
        le_csSup hbdd (I.sourceQPilotLogVolume_mem_valueSet v R n)
  exact le_antisymm hle hge

/-- Every possible theta-pilot image degree is bounded by the hull log-volume,
under the same boundedness/contraction hypotheses. This is the value-layer
comparison with the possible-image data. -/
theorem sourceImageLogDegree_le_sourceThetaHullLogVolume_of_contracted (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0)
    (j : SignedLabel l.value) :
    I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤
      I.sourceThetaHullLogVolume v R n := by
  have hbdd : BddAbove (I.sourceThetaHullLogValueSet v R n) :=
    I.sourceThetaHullLogValueSet_bddAbove_of_contracted v R n hq hScaling
  unfold sourceThetaHullLogVolume
  exact le_csSup hbdd
    ⟨I.sourceThetaPilotPoint v R n j,
      I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j, rfl⟩

/-- The q-pilot value lies below the hull log-volume, under the same
contraction hypotheses. This restates the base xi-f inclusion at the
value-layer surrogate; it is not the paper xi-f inclusion. -/
theorem sourceQPilotLogVolume_le_sourceThetaHullLogVolume_of_contracted (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  I.sourceXiFInclusion v R n hq hScaling

/-- Under the contracted-generator hypotheses the value-layer hull Haar volume
is actually zero, not merely finite: every point of the hull has nonpositive
log-degree, so it lies in the zero-volume negative-degree phase. This is another
explicit warning that the value-layer surrogate is not the paper's
positive finite `-|log Theta|` object. -/
theorem sourceHullVolume_eq_zero_of_q_le_one_and_scaling (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceHullVolume v R n = 0 :=
  I.sourceHullVolume_eq_zero_of_hull_logDegree_nonpos v R n (by
    intro x hx
    exact I.sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators
      v R n (I.sourceImageLogDegree_nonpos_of_q_le_one v R n hq)
      hScaling x hx)

/-- Under the contracted-generator hypotheses the actual source hull Haar volume
is finite. -/
theorem sourceHullVolume_lt_top_of_q_le_one_and_scaling (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceHullVolume v R n < ⊤ :=
  I.sourceHullVolume_lt_top_of_contractedGenerators v R n
    (I.sourceImageLogDegree_nonpos_of_q_le_one v R n hq) hScaling

/-- The actual possible-image/edge Haar volume is unconditionally finite. -/
theorem sourceImageVolume_lt_top_of_source (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceImageVolume v R n < ⊤ :=
  I.sourceImageVolume_lt_top v R n

/-- Under the same contraction hypotheses the actual hull Haar volume is bounded
by the actual possible-image/edge volume. -/
theorem sourceHullVolume_le_sourceImageVolume_of_q_le_one_and_scaling (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n :=
  I.sourceHullVolume_le_imageVolume_of_q_le_one_and_scaling v R n hq hScaling

/-- The signed hull log-volume is a real number (its `WithTop` coercion is
finite). This records the `Real` finiteness independently of the Haar volume. -/
theorem sourceThetaHullLogVolume_finite (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.sourceThetaHullLogVolume v R n : WithTop Real) < ⊤ :=
  WithTop.coe_lt_top _

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

end
