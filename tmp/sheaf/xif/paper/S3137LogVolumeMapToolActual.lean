import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-!
# TOOL: Haar log-volume transport along a measurable map (generic)

**Reusable mathematical tool, not a paper object.**  Owner: lattice.  We
MANUFACTURE the missing general tool that several streams need when a proof is
blocked by the absence of a transport lemma for Haar log-volumes:

* `haarLogVolume_map_of_preimage_eq`: if `T` is measurable and `f ⁻¹' T = S`,
  then the Haar log-volume of `T` for the pushforward measure `μ.map f` equals
  the Haar log-volume of `S` for `μ`;
* `haarLogVolume_map_image_of_injective`: the same for `T = f '' S` under
  injectivity of `f` (the exact shape used by pushforward/scaling arguments);
* `haarLogVolume_map_const_smul_image`: the scalar-scaling instance
  `T = c • S` under `f x = c • x` for `c ≠ 0` on a real vector space — the
  transport-invariance half of every `lambda`-scaling / V-form normalization
  argument (IUT III, Prop. 3.9, (i), p. 115; IUT IV, Prop. 1.4, (i)).

The tools are fully proved from the definition of `haarLogVolume` and
`Measure.map`; the INSTANTIATION data (measurability/continuity and the
specific measure) is left to the consumer as explicit hypotheses, so no
unavailable source datum is asserted.  Consumers: hull (raw-Haar -> V-form
channel), abc (F4(b1) pushforward scaling), lattice (log-shell scaling).
Source: IUT III, Prop. 3.9, (i), p. 115; IUT IV, Prop. 1.4, (i).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.LogVolumeMapToolActual

/-- **Generic tool: Haar log-volume transport along a measurable map.**  If `T`
is measurable and `f ⁻¹' T = S`, then the Haar log-volume of `T` under the
pushforward `μ.map f` equals the Haar log-volume of `S` under `μ`. -/
theorem haarLogVolume_map_of_preimage_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) {S : Set X} {T : Set Y}
    (hf : Measurable f) (hT : MeasurableSet T) (h : f ⁻¹' T = S) :
    haarLogVolume (μ.map f) T = haarLogVolume μ S := by
  unfold haarLogVolume
  rw [Measure.map_apply hf hT, h]

/-- **Generic tool: Haar log-volume transport along an injective measurable map.**
The pushforward measure's log-volume of the image equals the source log-volume. -/
theorem haarLogVolume_map_image_of_injective
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (S : Set X)
    (hf : Measurable f) (hinj : Function.Injective f)
    (hImage : MeasurableSet (f '' S)) :
    haarLogVolume (μ.map f) (f '' S) = haarLogVolume μ S :=
  haarLogVolume_map_of_preimage_eq μ f hf hImage (Set.preimage_image_eq S hinj)

/-- **Generic tool: scalar-scaling transport invariance.**  For `c ≠ 0` on a real
vector space, the Haar log-volume of the scaled set `c • S` under the pushed-
forward measure `μ.map (x ↦ c • x)` equals the Haar log-volume of `S` under
`μ`.  This is the transport-invariance half of the `lambda`-scaling / V-form
normalization arguments. -/
theorem haarLogVolume_map_const_smul_image
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    (μ : Measure E) (c : ℝ) (hc : c ≠ 0) (S : Set E)
    (hcont : Continuous fun x : E => c • x)
    (hImage : MeasurableSet ((fun x : E => c • x) '' S)) :
    haarLogVolume (μ.map (fun x : E => c • x))
        ((fun x : E => c • x) '' S) = haarLogVolume μ S := by
  refine haarLogVolume_map_image_of_injective μ (fun x : E => c • x) S
    hcont.measurable ?_ hImage
  intro x y hxy
  have h' := congrArg (fun z : E => c⁻¹ • z) hxy
  simpa [inv_smul_smul₀ hc] using h'

end LeanFormal.IUT.XiFPaper.LogVolumeMapToolActual