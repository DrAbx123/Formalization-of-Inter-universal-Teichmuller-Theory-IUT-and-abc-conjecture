import tmp.sheaf.xif.paper.S3139SourceMultiradialConsumerActual
import tmp.sheaf.xif.paper.S3139StageOneSeamsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: Stage-1 fourth-triangle consumer package

The consumer-facing package of the Stage-1 objects: actual BPS and etHT
(`S3139SourceBPSActual` / `S3139SourceEtHTActual`), the actual partial
multiradial quotient target (`S3139SourceMultiradialConsumerActual`), the exact
S3134 fourth-triangle supply record (`S3139StageOneSeamsActual`), and the
named q/Theta comparison input (the S3138 V2 pinned boundary).

From the package the fourth-triangle composite `(hull+det) circ (dsc)` readout
of S3134 is available at every place, its hull lattice is nonempty, and the
Corollary 3.12 ordered conclusion follows from the single named (xi-f)-shaped
inclusion.  This is the interface the lattice/mainline streams can fill with
their actual pilot log-volumes without editing this stream's files.

Source: IUT III, Theorem 3.11 and Corollary 3.12; Formalization of IUT
(2026-04) §4 :443-546, :602-621.  No sorry, axiom, True, PUnit, or toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139StageOneFourthTriangleConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3139SourceBPSActual
open LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual
open LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual.SourceEtHT
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual
open LeanFormal.IUT.XiFPaper.S3139StageOneSeamsActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual

universe u v ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-- The Stage-1 fourth-triangle consumer package.  Every supplied object is a
structure parameter (actual BPS/etHT, actual partial multiradial target, actual
S3134 consumer records, named q/Theta comparison input); the fields are the two
concrete named paper hypotheses connecting them (Theta-pilot gluing,
Formalization :507-513; 0-column etHT, :520-524). -/
structure StageOneFourthTrianglePackage
    (I31 : Input Label Choice) (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (hdd : S1300HDDHullDetSource I31)
    (she : SourceSHEHDDCompatibility (I := I31) (J := J))
    (comparison : SourceQThetaComparisonInput J)
    (bps : SourceBPS V) (etHT : SourceEtHT l V)
    (multiradial : SourceMultiradialTargetInput J) where
  /-- named hypothesis (Formalization :507-513): the algorithm-input BPS is
  glued by a full poly-isomorphism to the underlying BPS of the Theta-pilot -/
  bps_glued :
    Nonempty (SourceFTimesMuPrimeStripEquivalence bps.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip)
  /-- named hypothesis (Formalization :520-524): the etHT is the 0-column etHT -/
  etHT_zero_column : etHT = sourceEtHTZeroColumn J 0

/-- The canonical package: the constructible slots are built from the actual
original input, and both named seam hypotheses are discharged reflexively.
The supplied arguments are the actual S3134 records and the arithmetic
comparison data only. -/
theorem stageOneFourthTrianglePackage
    (I31 : Input Label Choice) (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (hdd : S1300HDDHullDetSource I31)
    (she : SourceSHEHDDCompatibility (I := I31) (J := J))
    (comparison : SourceQThetaComparisonInput J) :
    StageOneFourthTrianglePackage I31 J hdd she comparison
      (sourceBPSOfTheater J 0 0) (sourceEtHTZeroColumn J 0)
      (sourceMultiradialTargetInput J) where
  bps_glued := ⟨SourceFTimesMuPrimeStripEquivalence.refl _⟩
  etHT_zero_column := rfl

namespace StageOneFourthTrianglePackage

variable (I31 : Input Label Choice) (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (hdd : S1300HDDHullDetSource I31)
variable (she : SourceSHEHDDCompatibility (I := I31) (J := J))
variable (comparison : SourceQThetaComparisonInput J)

/-- The actual fourth-triangle composite @(hull+det) circ (dsc)@ readout at a
place, from the Stage-1 package data. -/
def composite (v : NumberField.FinitePlace ℚ) :=
  S3134FourthJointComposite I31 J hdd she v

theorem composite_fst (v : NumberField.FinitePlace ℚ) :
    (composite I31 J hdd she v).1 =
      S3134SHEReadout (I := I31) (J := J) she v
        (S3134SHEOutputObject (I := I31)) := rfl

/-- The hull lattice of the fourth-triangle composite is nonempty. -/
theorem composite_snd_nonempty (v : NumberField.FinitePlace ℚ) :
    (composite I31 J hdd she v).2.Nonempty :=
  S3134HullDetReadout_nonempty I31 hdd (S3134SHEOutputObject I31) v

/-- The Corollary 3.12 ordered conclusion (the q/Theta pilot log-volume
comparison heart) from the named comparison input. -/
theorem comparison_conclusion :
    Cor312Conclusion
      (comparison.boundary.assembly.arithmetic.toContract) :=
  comparison.conclusion

/-- The Stage-1 BPS underlying strip is the S3138 Step XI input's theater
strip: the Stage-1 input and the Step XI consumer read the same actual strip. -/
theorem bps_stepXI_strip (n m : Int) :
    (sourceBPSOfTheater J n m).underlying =
      (sourceStepXIInput J n m).theater.primeStrip :=
  sourceBPS_stepXIInput_underlying J n m

end StageOneFourthTrianglePackage

end LeanFormal.IUT.XiFPaper.S3139StageOneFourthTriangleConsumerActual

end
