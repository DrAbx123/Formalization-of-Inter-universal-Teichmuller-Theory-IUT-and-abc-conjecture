import tmp.sheaf.xif.paper.Mzk1G1CompactnessActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1CompactnessActual2
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1CompactnessActual

/-- Actual affine Fermat chart X^n + Y^n = 1 over ℚ. -/
def FermatChart (n : ℕ) : Type :=
  {p : ℚ × ℚ // p.1 ^ (n + 1) + p.2 ^ (n + 1) = 1}

/-- Actual point fields on the Fermat chart. -/
structure FermatChartPoint (n : ℕ) where
  chart : FermatChart n

/-- Actual G1 compactness data using the Fermat scheme and chart. -/
structure G1CompactnessActual2Data (n : ℕ) where
  schemeCompact : IsCompact (Set.univ : Set (FermatScheme n))
  chartPoint : FermatChartPoint n

noncomputable def g1CompactnessActual2Data (n : ℕ) : G1CompactnessActual2Data n where
  schemeCompact := fermatScheme_isCompact n
  chartPoint := ⟨⟨(0, 1), by simp [zero_pow (Nat.succ_ne_zero n)]⟩⟩

theorem g1CompactnessActual2Data_nonempty (n : ℕ) :
    Nonempty (G1CompactnessActual2Data n) :=
  ⟨g1CompactnessActual2Data n⟩

end LeanFormal.IUT.XiFPaper.G1CompactnessActual2
end
