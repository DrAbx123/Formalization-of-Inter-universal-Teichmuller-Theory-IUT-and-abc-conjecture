import tmp.sheaf.xif.paper.Mzk1R4LiteralAssemblyActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1R4EndgameCompositionActual — R4 endgame composition

One endgame file: the literal per-epsilon comparison family plus the
four-triangle synthesis on the literal interface feed `r4_literal_assembly`,
which yields the Cor 3.12 ordered conclusion, conditional ABC, and literal
hull log-volume finiteness.  The Stage-5 numerical readout
`abcFormAdditiveHeightBound_of_literalEstimates` is included as a fourth
conjunct; its two literal estimates remain explicit named hypotheses.
No closure claim; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R4EndgameCompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

theorem r4_endgame_composition {DSC SHEOut : Type*}
    (S : FourTriangleSynthesis DSC SHEOut) (j : Nat)
    (hcomp : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison
        (literalIQInterface (C3 := C3) j) epsilon)
    (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    Cor312Conclusion S.contract ∧ ABCConjecture ∧
      globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      ABCFormAdditiveHeightBound := by
  obtain ⟨hcor, habc, hfin⟩ := r4_literal_assembly (C3 := C3) S j hcomp
  exact ⟨hcor, habc, hfin,
    abcFormAdditiveHeightBound_of_literalEstimates logVolume hullVolume hheight hmain⟩

end LeanFormal.IUT.XiFPaper.Mzk1R4EndgameCompositionActual

end
