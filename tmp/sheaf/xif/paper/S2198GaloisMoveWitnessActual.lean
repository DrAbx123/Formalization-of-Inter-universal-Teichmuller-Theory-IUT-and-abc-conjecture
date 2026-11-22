import tmp.sheaf.xif.paper.S2184GaloisMoveActual
import Mathlib.FieldTheory.Galois.Infinite

/-! # S2198: from non-base primitive root to an actual Galois move

Given the exact missing proof that the constructed primitive root of S2174 is
not in the base completion, the infinite Galois correspondence produces an actual
local Galois automorphism moving it.  This reduces the S2174 Galois-move gap to
the single not-in-base statement, with no second-root choice. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2198GaloisMoveWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2174CyclotomicWitnessActual
open LeanFormal.IUT.XiFPaper.S2184GaloisMoveActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- If the constructed primitive root is not in the base completion, the local
Galois group moves it. -/
theorem s2198_exists_galois_move_of_notInBase
    (n : Nat) (hn : 0 < n)
    (hnot : S2184PrimitiveRootNotInBaseRequired T b n hn) :
    ∃ σ : S2147PaperIntegralClosureGaloisGroup T b,
      σ (s2174PrimitiveRoot T b n hn) ≠ s2174PrimitiveRoot T b n hn := by
  classical
  by_contra h
  push_neg at h
  have hfix : s2174PrimitiveRoot T b n hn ∈
      (⊥ : IntermediateField (NormalizedCompletion (sectionKPlace T b))
        (S2147PaperIntegralClosure T b)) := by
    rw [InfiniteGalois.mem_bot_iff_fixed]
    intro σ
    exact h σ
  exact hnot (IntermediateField.mem_bot.mp hfix)

/-- Exact missing not-in-base datum for some constructed primitive root. -/
structure S2198NotInBaseRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  n : Nat
  hn : 0 < n
  notInBase : S2184PrimitiveRootNotInBaseRequired T b n hn

/-- A not-in-base datum gives an actual Galois move and hence the S2174 missing
structure. -/
noncomputable def s2198GaloisMovesRootRequired
    (M : S2198NotInBaseRequired T b) :
    S2174GaloisMovesRootRequired T b M.n M.hn :=
  let σ := Classical.choose
    (s2198_exists_galois_move_of_notInBase T b M.n M.hn M.notInBase)
  { σ := σ
    hσ := Classical.choose_spec
      (s2198_exists_galois_move_of_notInBase T b M.n M.hn M.notInBase) }

/-- The S2174 exact missing Galois move follows from a not-in-base datum. -/
theorem s2198GaloisMovesPrimitiveRootRequired_of_notInBase
    (M : S2198NotInBaseRequired T b) :
    S2174GaloisMovesPrimitiveRootRequired T b :=
  ⟨M.n, M.hn, ⟨s2198GaloisMovesRootRequired T b M⟩⟩

#check s2198_exists_galois_move_of_notInBase
#check S2198NotInBaseRequired
#check s2198GaloisMovesRootRequired
#check s2198GaloisMovesPrimitiveRootRequired_of_notInBase

end LeanFormal.IUT.XiFPaper.S2198GaloisMoveWitnessActual
end
