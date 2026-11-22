import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2756FractionalIdealHaarActual

open MeasureTheory MeasureTheory.Measure Module ZSpan Submodule
open NumberField NumberField.mixedEmbedding
open scoped ENNReal NNReal nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Haar-measurable fundamental domain of the lattice of a nonzero
fractional ideal in the mixed space. -/
def S2756IdealFundamentalDomain (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    Set (NumberField.mixedEmbedding.mixedSpace K) :=
  ZSpan.fundamentalDomain (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I)

/-- Actual set-level Haar volume of the fractional-ideal fundamental domain. -/
noncomputable def S2756IdealHaarVolume
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) : ENNReal :=
  volume (S2756IdealFundamentalDomain K I)

/-- Actual Haar volume formula: the fundamental domain volume is the ideal norm
times the volume of the integer-lattice fundamental domain. -/
theorem S2756IdealHaarVolume_eq
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    S2756IdealHaarVolume K I =
      ENNReal.ofReal (FractionalIdeal.absNorm I.1) *
        volume (ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis K)) := by
  simpa [S2756IdealHaarVolume, S2756IdealFundamentalDomain] using
    (NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis K I)

/-- Actual Haar covolume of the fractional-ideal lattice: norm times the
discriminant/mixed-space normalization. -/
theorem S2756IdealCovolume_eq
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    ZLattice.covolume (NumberField.mixedEmbedding.idealLattice K I) =
      (FractionalIdeal.absNorm I.1) *
        ((2 : ℝ)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)| :=
  NumberField.mixedEmbedding.covolume_idealLattice K I

/-- The canonical actual log-volume of a fractional ideal, defined from the Haar
covolume of its lattice (not an indicator). -/
noncomputable def S2756IdealLogVolume
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) : Real :=
  Real.log (ZLattice.covolume (NumberField.mixedEmbedding.idealLattice K I))

#check S2756IdealFundamentalDomain
#check S2756IdealHaarVolume
#check S2756IdealHaarVolume_eq
#check S2756IdealCovolume_eq
#check S2756IdealLogVolume
#print axioms S2756IdealHaarVolume_eq
#print axioms S2756IdealCovolume_eq
end LeanFormal.IUT.XiFPaper.S2756FractionalIdealHaarActual
end
