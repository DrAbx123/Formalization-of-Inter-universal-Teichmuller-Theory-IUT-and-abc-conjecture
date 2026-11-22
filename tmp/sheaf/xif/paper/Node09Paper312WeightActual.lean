import tmp.sheaf.xif.paper.Mzk1Paper312AssemblyActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

namespace LeanFormal.IUT.XiFPaper.Node09Paper312WeightActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (FinitePlaceAtPrime F p)]

/-- The actual q_v fiber weight: qV effective multiplicity (order times local
residue degree), as a real weight. -/
noncomputable def qVWeight
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S)) :
    FinitePlaceAtPrime F p → ℝ :=
  fun i => (qVEffectiveMultiplicity X (b i) : ℝ)

/-- The qV weight times the base residue norm log is the actual q_v local log
magnitude. -/
theorem qVWeight_log_eq_localLogMagnitude
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (i : FinitePlaceAtPrime F p) :
    qVWeight X b i * Real.log (residueNormBase (b i).1) =
      localLogMagnitude (qVFamily X.S (b i)) :=
  (qVFamily_localLogMagnitude_eq (X := X) (b := b i)).symm

/-- The mult-weighted fiber A-bound from the per-place qV-weighted bound. -/
theorem A_le_Lbar_add_Dbar_of_qVWeight
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    {Fdeg logp logIdx diff : FinitePlaceAtPrime F p → ℝ} {l : ℝ}
    (h : ∀ i : FinitePlaceAtPrime F p,
      qVWeight X b i / (Fdeg i * (2 * l)) * logp i ≤ logIdx i + diff i) :
    (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        qVWeight X b i / Fdeg i * logp i) ≤
      ∑ i : FinitePlaceAtPrime F p, (logIdx i + diff i) :=
  A_le_Lbar_add_Dbar_of_correction h

/-- The 3.12 assembly for the actual qV-weighted fiber A-term. -/
theorem paper312_of_qVWeight
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg : FinitePlaceAtPrime F p → ℝ) (l : ℝ)
    (logp logIdx diff : FinitePlaceAtPrime F p → ℝ)
    (sFactor : ℝ) (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
      qVWeight X b i / Fdeg i * logp i))
    (h : ∀ i : FinitePlaceAtPrime F p,
      qVWeight X b i / (Fdeg i * (2 * l)) * logp i ≤ logIdx i + diff i) :
    ExplicitPaper312Inequality sFactor
      ((1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        qVWeight X b i / Fdeg i * logp i))
      (∑ i : FinitePlaceAtPrime F p, logIdx i)
      (∑ i : FinitePlaceAtPrime F p, diff i) :=
  paper312_of_correction_bounds hs0 hs1 hA0
    (fn := fun i => qVWeight X b i)
    (Fdeg := Fdeg) (logp := logp) (logIdx := logIdx) (diff := diff) h

/-- Exact remaining missing for the qV-weighted 3.12 consumer. -/
def Node09Paper312WeightRemainingMissing : List String :=
  [ "hA0: nonnegativity of the qV-weighted A-term (provable from qVEffectiveMultiplicity and prime-log nonnegativity)",
    "hlogp: logp i = Real.log (residueNormBase (b i).1) (Fmod = Q residue-norm / rational-prime identification)",
    "hper: paper 3.12 per-place qV-weighted inequality (core arithmetic estimate)" ]

end LeanFormal.IUT.XiFPaper.Node09Paper312WeightActual
