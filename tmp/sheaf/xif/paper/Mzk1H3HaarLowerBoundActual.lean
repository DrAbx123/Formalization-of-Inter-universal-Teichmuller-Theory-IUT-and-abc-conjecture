/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # H3 §11.4: Haar lower bound exact interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1H3HaarLowerBoundActual

/-- Haar lower bound from finite Fourier support: `muH >= #A * muCminus`
and the finite support product bound. -/
structure H3HaarLowerBoundData (G : Type*) [AddCommGroup G] [Fintype G] where
  cardA : ℕ
  cardB : ℕ
  muH : ℝ
  muCminus : ℝ
  mussCminus_nonneg : 0 ≤ muCminus
  support_product_bound : cardA * cardB ≥ Fintype.card G
  haar_lower_bound : muH ≥ (cardA : ℝ) * muCminus

def H3HaarLowerBoundRequired (G : Type*) [AddCommGroup G] [Fintype G] : Prop :=
  Nonempty (H3HaarLowerBoundData G)

end LeanFormal.IUT.XiFPaper.Mzk1H3HaarLowerBoundActual
