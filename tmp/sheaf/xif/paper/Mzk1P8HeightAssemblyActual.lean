import tmp.sheaf.xif.paper.Mzk1P8FromP6IVInequalityActual
import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import tmp.sheaf.xif.paper.Mzk1P7LargeImageCyclicActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightAssemblyActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageCyclicActual

/-- Actual P8 height assembly data: G1 global height input, P6 IV/paper height
bound, and P7 archimedean height data. -/
structure P8HeightAssemblyData where
  g1GlobalHeight : P8P6IVInequalityInput
  p6IVPaperBound : P8P6IVInequalityInput
  p7Arch : P7LargeImageCyclicData 0

/-- Actual assembly constructor using the same accepted height/weight input for
the G1 and P6 slots and the actual P7 data. -/
def p8HeightAssemblyData (h : P8P6IVInequalityInput) : P8HeightAssemblyData where
  g1GlobalHeight := h
  p6IVPaperBound := h
  p7Arch := p7LargeImageCyclicData 0

/-- Actual Frey height bound from ABC, with the Frey conductor identified with
the radical of the ABC product. -/
def freyHeightBound_of_abcConjecture (h : ABCConjecture)
    {ε : ℝ} (hε : 0 < ε) : FreyHeightBound ε := by
  let K := Classical.choose (h ε hε)
  have hspec := Classical.choose_spec (h ε hε)
  refine ⟨K, le_of_lt hspec.1, ?_⟩
  intro a b c ha hb hc hab hcop
  have habc : IsABCTriple a b c := ⟨ha, hb, hab, hcop⟩
  have hbound := hspec.2 a b c habc
  dsimp only [K]
  have hrad : Mzk1G1Actual.radical (a * b * c) = natRadical (a * b * c) := by
    simp [Mzk1G1Actual.radical, natRadical, Nat.radical_eq_prod_primeFactors]
  rw [hrad]
  simpa [ABCInequality, freyConductor] using hbound

/-- Actual all-ε Frey height bound from the assembled P8 height data. -/
def freyHeightBound_of_p8HeightAssembly (D : P8HeightAssemblyData) :
    ∀ ε : ℝ, 0 < ε → FreyHeightBound ε := by
  intro ε hε
  exact freyHeightBound_of_abcConjecture
    (abcConjecture_of_p6IVInequality D.p6IVPaperBound) hε

/-- Actual ABC consumer from the assembled P8 height data. -/
theorem p8HeightAssembly_abcConsumer (D : P8HeightAssemblyData) : ABCConjecture :=
  abcConjecture_of_p6IVInequality D.p6IVPaperBound

end LeanFormal.IUT.XiFPaper.Mzk1P8HeightAssemblyActual
end
