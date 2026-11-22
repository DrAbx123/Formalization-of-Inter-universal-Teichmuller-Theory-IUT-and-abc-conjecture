import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Bases

/-! # S1190: fixed-subgroup lemma for the product evaluation

G = (v : V) -> upper.Pi v, eval_v : G -> upper.Pi v.
For every open subgroup H of G, the image eval_v '' H is an open subgroup of
upper.Pi v (projection is an open map), and

  fixedSubgroup (upper.unitsAction v) (image) =
  fixedSubgroup ((upper.unitsAction v).comp (eval v)) H.

The equality is purely subgroup-theoretic: for every g in the image, choose
h in H with eval_v h = g.  No indiscrete-topology hypothesis is needed for the
equality; openness of the image is supplied by isOpenMap_eval. -/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1190EvalFixedSubgroupActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe uv
variable {V : Type uv}
variable {upper : FPrimeStrip V}
variable [∀ v : V, TopologicalSpace (upper.Pi v)]

/-- The product evaluation group G = (v : V) -> upper.Pi v. -/
abbrev GraphGroup : Type _ := (v : V) → upper.Pi v

/-- Image of an open subgroup under the projection eval_v. -/
noncomputable def evalOpenSubgroup (H : OpenSubgroup (GraphGroup (upper := upper))) (v : V) :
    OpenSubgroup (upper.Pi v) where
  carrier := Function.eval v '' (H : Set (GraphGroup (upper := upper)))
  one_mem' := ⟨1, H.one_mem, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, H.mul_mem ha hb, rfl⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, H.inv_mem ha, rfl⟩
  isOpen' := by
    change IsOpen (Function.eval v '' (H : Set (GraphGroup (upper := upper))))
    exact isOpenMap_eval (X := upper.Pi) v (H : Set (GraphGroup (upper := upper))) H.isOpen

/-- The fixed-subgroup equality for the product evaluation. -/
theorem fixedSubgroup_evalOpenSubgroup
    (H : OpenSubgroup (GraphGroup (upper := upper))) (v : V) :
    TimesMuKummer.fixedSubgroup (upper.unitsAction v) (evalOpenSubgroup H v) =
      TimesMuKummer.fixedSubgroup
        ((upper.unitsAction v).comp (Pi.evalMonoidHom upper.Pi v)) H := by
  ext u
  constructor
  · intro hu h
    exact hu ⟨Function.eval v (h : GraphGroup (upper := upper)), ⟨h, h.2, rfl⟩⟩
  · intro hu g
    rcases g.2 with ⟨h, hh, hgy⟩
    have hh' := hu ⟨h, hh⟩
    simpa [hgy] using hh'

end LeanFormal.IUT.XiFPaper.S1190EvalFixedSubgroupActual
end