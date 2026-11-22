import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1HullInequalityReductionChainActual — A479 real consumer theorems

New conclusions combining the existing H5 hull-volume reduction theorems of
`CardHullRealGeometryReduction.lean` (the file itself records that the
unconditional `hull <= image` inequality is not a formal consequence of the
data; these theorems make the *reduction chain* and its consequences explicit):

1. `hull_eq_iff_forall_pointVolume_le`: hull/image equality is equivalent to the
   pointwise upper bound on the hull (composition of the equality/inequality
   equivalence :152 with the pointwise reduction :162);
2. `hull_eq_iff_forall_pointVolume_le_labelSup`: the same in label-sup form
   (equality/inequality + pointwise reduction :181 + the possible-image-volume
   identification);
3. `hullVolume_le_imageVolume_necessary_package`: the inequality implies the
   image-product and scaling-unit point-volume bounds jointly (:243/:260);
4. `hull_eq_of_generator_nonpos`: in the contractive/neutral regime
   (nonpositive local log-degree for all generators, :324) the **equality**
   form holds (not just the inequality).

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullInequalityReductionChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

/-- Equality of hull/image volumes is equivalent to the pointwise bound over
the hull. -/
theorem hull_eq_iff_forall_pointVolume_le {l : PrimeGeFive} {V : Type*}
    (I : OriginalInput l V) (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n =
        I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ↔
      ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v x ≤
          I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  (sourceHullVolume_eq_imageVolume_iff I v R n).trans
    (sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le I v R n)

/-- Equality of hull/image volumes is equivalent to the pointwise bound in the
label-sup form. -/
theorem hull_eq_iff_forall_pointVolume_le_labelSup {l : PrimeGeFive} {V : Type*}
    (I : OriginalInput l V) (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n =
        ⨆ j : SignedLabel l.value,
          ENNReal.ofReal
            (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j)) ↔
      ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v x ≤
          ⨆ j : SignedLabel l.value,
            ENNReal.ofReal
              (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j)) := by
  rw [sourceHullVolume_eq_imageVolume_iff,
    ← sourceSetVolume_possibleImageSet_eq_labelSup (I := I) v R n]
  exact sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le I v R n

/-- Necessary-condition package for the remaining hull/image inequality:
image products and scaling units both stay below the image-union volume. -/
theorem hullVolume_le_imageVolume_necessary_package {l : PrimeGeFive} {V : Type*}
    (I : OriginalInput l V) (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hV : I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) :
    (∀ j j' : SignedLabel l.value,
        I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j *
          I.sourceThetaPilotPoint v R n j') ≤
          I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) ∧
      (∀ s ∈ I.sourceScalingUnits v,
        I.sourcePointVolume v s ≤
          I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) :=
  ⟨fun j j' => sourcePointVolume_imageProduct_le_of_hullVolume_le_imageVolume I v R n hV j j',
   fun s hs => sourcePointVolume_scaling_le_of_hullVolume_le_imageVolume I v R n hV hs⟩

/-- **Equality form in the contractive/neutral regime.** If every generator has
nonpositive local log-degree-sum, the hull/image equality holds (not merely the
inequality). -/
theorem hull_eq_of_generator_nonpos {l : PrimeGeFive} {V : Type*}
    (I : OriginalInput l V) (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hscal : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceHullVolume v R n =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  (sourceHullVolume_eq_imageVolume_iff I v R n).mpr
    (sourceHullVolume_le_imageVolume_of_generator_nonpos I v R n himg hscal)

#check hull_eq_of_generator_nonpos
#check hull_eq_iff_forall_pointVolume_le_labelSup

end LeanFormal.IUT.XiFPaper.Mzk1HullInequalityReductionChainActual
end