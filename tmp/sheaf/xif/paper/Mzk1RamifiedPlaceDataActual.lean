/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RamifiedPlaceActual
import tmp.sheaf.xif.paper.Mzk1Paper312UnramifiedActual
import Mathlib.Tactic
/-! # Place-indexed ramified data and accumulated per-place bounds -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1RamifiedPlaceDataActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1RamifiedPlaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312UnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312CorrectionConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
open scoped NNReal NormedField
universe u

/-- Scalar per-place data; local-field instances live in `places`. -/
structure RamifiedPlaceData (ι : Type u) [Fintype ι] where
  places : ι → RamifiedPlace.{u}
  fn : ι → Nat
  mult : ι → ℝ
  Fdeg : ι → ℝ
  l : ℝ
  logp : ι → ℝ
  logMu : ι → ℝ
  logIdx : ι → ℝ
  diff : ι → ℝ
  aExp : ι → Nat
  cCorr : ι → Nat
variable {ι : Type u} [Fintype ι]

/-- Per-place correction hypothesis, with instances supplied by `places`. -/
def HasCorrection (d : RamifiedPlaceData ι) : Prop :=
  ∀ i,
    letI := (d.places i).normed
    letI := (d.places i).charZero
    letI := (d.places i).complete
    letI := (d.places i).ultrametric
    letI := (d.places i).proper
    letI := (d.places i).factPrime
    letI := (d.places i).alg
    letI := (d.places i).finDim
    LogShellResiduePowerCardCorrectionHypothesis (K := (d.places i).K)
      (p := (d.places i).p) (d.aExp i) (d.cCorr i)
/-- Per-place log-index identification. -/
def HasLogIdx (d : RamifiedPlaceData ι) : Prop :=
  ∀ i,
    letI := (d.places i).normed
    letI := (d.places i).charZero
    letI := (d.places i).complete
    letI := (d.places i).ultrametric
    letI := (d.places i).proper
    letI := (d.places i).factPrime
    letI := (d.places i).alg
    letI := (d.places i).finDim
    d.logIdx i = Real.log (logShellIntegerIndex (K := (d.places i).K)
      (p := (d.places i).p) : ℝ)
/-- Per-place coefficient comparison. -/
def HasCoeff (d : RamifiedPlaceData ι) : Prop :=
  ∀ i, CoeffComparison ((d.fn i : ℝ)) (d.Fdeg i) d.l ((d.aExp i : ℝ))
/-- Per-place residue-card power identity. -/
def HasRes (d : RamifiedPlaceData ι) : Prop :=
  ∀ i,
    letI := (d.places i).normed
    letI := (d.places i).charZero
    letI := (d.places i).complete
    letI := (d.places i).ultrametric
    letI := (d.places i).proper
    letI := (d.places i).factPrime
    letI := (d.places i).alg
    letI := (d.places i).finDim
    logShellResidueCard (K := (d.places i).K) =
      (d.places i).p ^ d.fn i
/-- Accumulated per-place correction bounds. -/
theorem perPlace_bounds_of_data
    {ι : Type u} [Fintype ι] (d : RamifiedPlaceData ι)
    (hcard : HasCorrection d) (hlogIdx : HasLogIdx d)
    (hcoef : HasCoeff d) (hres : HasRes d)
    (hlogp_eq : ∀ i, d.logp i = Real.log ((d.places i).p : ℝ))
    (hmu0 : ∀ i, 0 ≤ d.logMu i) (hl : 1 ≤ 2 * d.l)
    (hc : ∀ i, 1 ≤ d.cCorr i)
    (hdiff : ∀ i, d.diff i = d.logMu i - (1 / (2 * d.l)) * d.logIdx i) :
    ∀ i, (d.fn i : ℝ) / (d.Fdeg i * (2 * d.l)) * d.logp i ≤
      d.logIdx i + d.diff i := by
  intro i
  dsimp [HasCorrection] at hcard
  dsimp [HasLogIdx] at hlogIdx
  dsimp [HasCoeff] at hcoef
  dsimp [HasRes] at hres
  letI := (d.places i).normed
  letI := (d.places i).charZero
  letI := (d.places i).complete
  letI := (d.places i).ultrametric
  letI := (d.places i).proper
  letI := (d.places i).factPrime
  letI := (d.places i).alg
  letI := (d.places i).finDim
  exact perPlace_diff_of_correction (K := (d.places i).K) (p := (d.places i).p)
    (hcard i) (hres i) (hcoef i) (hlogp_eq i) (hmu0 i) hl
    (hc i) (hlogIdx i) (hdiff i)
end LeanFormal.IUT.XiFPaper.Mzk1RamifiedPlaceDataActual
end