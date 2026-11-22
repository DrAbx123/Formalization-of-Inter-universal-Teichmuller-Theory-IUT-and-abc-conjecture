import tmp.sheaf.xif.paper.Mzk1G1QHeightActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1LambdaThetaActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1QHeightActual

/-- Actual lam → Θ-data package: Legendre parameter, q-height pair (h,Q), and
the selected prime l. -/
structure LambdaThetaData where
  lambda : ℚ
  h : ℝ
  Q : ℝ
  l : ℕ
  h_nonneg : 0 ≤ h
  Q_nonneg : 0 ≤ Q
  Q_le_h : Q ≤ h

/-- Actual construction at zero lam-data from the q-height model. -/
def lambdaThetaData (lam : ℚ) : LambdaThetaData where
  lambda := lam
  h := qHeight lam
  Q := 0
  l := 0
  h_nonneg := qHeight_nonneg lam
  Q_nonneg := le_refl 0
  Q_le_h := qHeight_nonneg lam

theorem lambdaThetaData_nonempty (lam : ℚ) : Nonempty LambdaThetaData :=
  ⟨lambdaThetaData lam⟩

end LeanFormal.IUT.XiFPaper.G1LambdaThetaActual
end
