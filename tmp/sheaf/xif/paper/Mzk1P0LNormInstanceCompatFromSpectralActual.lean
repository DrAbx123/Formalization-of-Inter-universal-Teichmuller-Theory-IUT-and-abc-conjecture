/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormBySpectralUniqueness
import tmp.sheaf.xif.paper.Mzk1P0LQThetaComponentActual
import tmp.sheaf.xif.paper.Mzk1P2NormalizedCompletionNormCoherenceActual
import Mathlib.Tactic

/-! # P0-L: CommonPrimeNormInstanceCompat from the general normalized-norm formula -/

The donor proves `‖x‖ = absNorm^{-(nu x / d)}` for the adic completion, and its
spectral identification identifies the normalized completion norm with the same formula.
Hence the adic and common-prime (normalized) norms should agree; the remaining point is
the type presentation equality, isolated in the first error if it fails. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormInstanceCompatFromSpectralActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaComponentActual
open LeanFormal.IUT.XiFPaper.Mzk1P2NormalizedCompletionNormCoherenceActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

theorem commonPrimeNormInstanceCompat_spectral :
    CommonPrimeNormInstanceCompat I place := by
  refine ⟨?_⟩
  intro x
  simpa using normalized_norm_eq_commonPrimeCompletion
    (place := (C3LAt I place).place) x

def compatSpectralRows : List (String × String × String) :=
  [ ("commonPrimeNormInstanceCompat_spectral", "compat via general normalized norm formula", "ATTEMPT") ]

theorem compatSpectralRows_length : compatSpectralRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0LNormInstanceCompatFromSpectralActual

end