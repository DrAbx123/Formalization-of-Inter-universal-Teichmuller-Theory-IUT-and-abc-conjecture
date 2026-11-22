import tmp.sheaf.xif.paper.S2810SourceImageHdegActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2812DegreeFaithfulSectionActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V}

/-- A section of the degree map is a monoid hom from the positive reals
whose log-degree is the identity. -/
def S2812DegreeFaithfulSection (v : V) : Prop :=
  ∃ s : Multiplicative Real →* I.ValueMonoidAt 0 0 v,
    ∀ b : Real, I.logDegreeAt 0 0 v (s (Multiplicative.ofAdd b)) = b

/-- If every value has nonpositive log-degree, no degree-faithful section
can exist: at `b = 1` the section would force `1 ≤ 0`. -/
theorem S2812_no_section_of_logDegree_nonpos
    (hnonpos : ∀ x : I.ValueMonoidAt 0 0 v, I.logDegreeAt 0 0 v x ≤ 0) :
    ¬ S2812DegreeFaithfulSection I v := by
  rintro ⟨s, hs⟩
  have h1 := hs 1
  have hp : I.logDegreeAt 0 0 v (s (Multiplicative.ofAdd (1 : Real))) ≤ 0 :=
    hnonpos _
  rw [h1] at hp
  norm_num at hp

/-- The actual source-Haar value monoid has nonpositive degree on every value. -/
theorem S2812_sourceHaarActual_logDegree_nonpos
    (S : SourceDefinition31Data.{ua} l) (n m : Int)
    (x : SourceHaarActualValueMonoid) :
    (sourceHaarActualOriginalInput (l := l) S).logDegreeAt n m () x ≤ 0 := by
  rw [sourceHaarActual_logDegreeAt_eq]
  exact (Multiplicative.toAdd x).property

/-- Exact no-go on the existing actual source-Haar carrier: no monoid section
from the positive reals can have degree `b` for all real `b`. -/
theorem S2812_sourceHaarActual_no_degreeFaithfulSection
    (S : SourceDefinition31Data.{ua} l) :
    ¬ ∃ s : Multiplicative Real →* SourceHaarActualValueMonoid,
        ∀ b : Real,
          (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 ()
            (s (Multiplicative.ofAdd b)) = b := by
  rintro ⟨s, hs⟩
  have h1 := hs 1
  have hp : (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 ()
      (s (Multiplicative.ofAdd (1 : Real))) ≤ 0 :=
    S2812_sourceHaarActual_logDegree_nonpos (l := l) S 0 0 _
  rw [h1] at hp
  norm_num at hp

#check S2812DegreeFaithfulSection
#check S2812_no_section_of_logDegree_nonpos
#check S2812_sourceHaarActual_logDegree_nonpos
#check S2812_sourceHaarActual_no_degreeFaithfulSection
#print axioms S2812_sourceHaarActual_no_degreeFaithfulSection

end LeanFormal.IUT.XiFPaper.S2812DegreeFaithfulSectionActual
end
