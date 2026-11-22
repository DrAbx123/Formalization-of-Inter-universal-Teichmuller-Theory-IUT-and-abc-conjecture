import tmp.sheaf.xif.paper.Mzk1Paper312AssemblyActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1Paper312AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

namespace LeanFormal.IUT.XiFPaper.Node09Paper312RatActual

variable {ι : Type*} [Fintype ι]

/-- Exact interface: the 3.12 assembly for a mult-weighted A-term, with the
per-place mult-weighted bound as an explicit hypothesis. -/
theorem paper312_of_mult
    {l sFactor : ℝ} (mult Fdeg logp logIdx diff : ι → ℝ)
    (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ (1 / (2 * l)) * (∑ i, mult i / Fdeg i * logp i))
    (hper : ∀ i, mult i / (Fdeg i * (2 * l)) * logp i ≤ logIdx i + diff i) :
    ExplicitPaper312Inequality sFactor
      ((1 / (2 * l)) * (∑ i, mult i / Fdeg i * logp i))
      (∑ i, logIdx i) (∑ i, diff i) :=
  paper312_of_correction_bounds hs0 hs1 hA0
    (fn := mult) (Fdeg := Fdeg) (logp := logp)
    (logIdx := logIdx) (diff := diff) hper

/-- Exact remaining missing for the Fmod = Q actual instantiation of the
mult-weighted 3.12 consumer. -/
def Node09Paper312RatRemainingMissing : List String :=
  [ "hbase: Nonempty (FinitePlaceQCandidate (nativeBadBasePlace X)) via actual RelativeNormQProperties",
    "hmult: mult i = qVEffectiveMultiplicity X (b i) (fiberMult/qV donor; Node09HqMultConsumerActual)",
    "hlogp: logp i = Real.log (residueNormBase (b i).1) (Fmod = Q residue-norm / rational-prime identification)",
    "hper: paper 3.12 per-place mult-weighted inequality (core arithmetic estimate)" ]

end LeanFormal.IUT.XiFPaper.Node09Paper312RatActual
