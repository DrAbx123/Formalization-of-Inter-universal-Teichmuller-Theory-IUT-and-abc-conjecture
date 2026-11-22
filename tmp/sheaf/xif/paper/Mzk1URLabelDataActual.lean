/-
# U-C label data (T-side definitions for david's (A) hVh)

ADAPTER-only definitions from existing API; no new mathematics.  Retained geometric
interface (varpi/Phi/hS/hexc) is documented in the header and will be added as a
named NO INHABITANT structure in the next batch.
-/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory

universe u v w

/-- lambda_j = j^2 * oq / (2*l), pure real. -/
noncomputable def labelLambda (l oq : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ 2 * oq / (2 * l)

/-- log p_b. -/
noncomputable def labelLogP (p : ℕ) : ℝ := Real.log (p : ℝ)

/-- D_b = d * log p_b. -/
noncomputable def labelD (d logp : ℝ) : ℝ := d * logp

/-- Q_b = oq * log p_b. -/
noncomputable def labelQ (oq logp : ℝ) : ℝ := oq * logp

/-- T_b = paper T = l*_mod log(s<=) at e*_mod. -/
noncomputable def labelTl (eMod : ℕ) (l : ℝ) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod l

section Tuple

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- delta = sum_i localNormOrder(different_i). -/
noncomputable def labelDifferentSum : ℝ :=
  ∑ i, localNormOrder p (arithmeticTupleLocalDifferent places tuple i)

/-- a = sum_i arithmeticTupleStepVA_i. -/
noncomputable def labelStepVASum : ℝ :=
  ∑ i, arithmeticTupleStepVA places tuple i

/-- labelM j = floor(lambda_j - delta - a). -/
noncomputable def labelM (l oq : ℝ) (j : ℕ) : ℤ :=
  ⌊labelLambda l oq j - labelDifferentSum places tuple - labelStepVASum places tuple⌋

end Tuple



/-- RETAINED geometric interface for (A) hVh (NO INHABITANT).
Fields (david 2026-11-17 shape): varpi, hvarpi_ne, hvarpi_order, Phi (= p6Phi),
hPhi_ne, hPhi_unit, hullSet (the actual per-label hull = the accepted L814 LHS
arithmeticTupleHolomorphicHull … (arithmeticTupleStepVPossibleImages …)), small_outside,
hexc.  The concrete instantiation of hullSet (with the actual AlgEquiv e and the
packet tensor block) is left to the consumer, which avoids universe bookkeeping
here.  Provenance: route section 5.4 Step(v)-(vi); accepted donor
FinitePlaceStepVAssembly L814. -/
structure LabelStepVHullData {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (istar : ι) (exceptional : Finset ι) (n : ℕ) (oq : ℝ) (eMod : ℕ)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)] where
  /-- per-label Kummer element (kurt: varpi_j = urRootAlpha^(j^2)) -/
  varpi : ℕ → CommonPrimeCompletion (places istar (tuple istar))
  hvarpi_ne : ∀ j, varpi j ≠ 0
  /-- paper order relation localNormOrder varpi_j = labelLambda_j -/
  hvarpi_order : ∀ j, localNormOrder p (varpi j) = labelLambda (2 * (n : ℝ) + 1) oq j
  /-- per-label unit-log preserving automorphism family Phi_j (= p6Phi) -/
  Phi : ℕ → Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple)
  hPhi_ne : ∀ j, (Phi j).Nonempty
  hPhi_unit : ∀ j, ∀ phi ∈ Phi j, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
    phi u ∈ arithmeticTupleUnitLogLattice places tuple
  /-- the actual per-label hull (instantiates the accepted L814 LHS) -/
  hullSet : ℕ → Set (ArithmeticTensorTupleBlock places tuple)
  /-- exceptional set is the true exceptional set -/
  small_outside : ∀ i, i ∉ exceptional →
    logShellRamificationExponent (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2
  /-- exceptional / R4 bound for every label -/
  hexc : ∀ j, (∑ i ∈ exceptional, (3 + Real.log
      (logShellRamificationExponent (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)))
    ≤ 4 * ((j : ℝ) + 1) * labelTl eMod (2 * (n : ℝ) + 1)
  /-- the accepted L814 output for hullSet (provenance:
  FinitePlaceStepVAssembly.arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound;
  hvarpi_order rewrites localNormOrder (varpi j) to labelLambda). -/
  hpaper : ∀ j : ℕ,
    arithmeticTupleNormalizedLogVolume places tuple Measure.addHaar (hullSet j) ≤
      (-labelLambda (2 * (n : ℝ) + 1) oq j + labelDifferentSum places tuple + 1) * labelLogP p +
        ∑ i ∈ exceptional, (3 + Real.log
          (logShellRamificationExponent (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ))
end LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual
end