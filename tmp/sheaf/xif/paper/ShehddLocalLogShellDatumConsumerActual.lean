import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

/-!
# ShehddLocalLogShellDatumConsumerActual — actual local log-shell datum consumer

STEP 0 prior-art (reuse only; A475 search: actual local log-shell datum found):
* IUTII/Kummer/SourceLocalLogShellDatum.lean: sourceLogShellStar_eq_logShellScale,
  sourceLocalLogShellDatum (pStar = logShellScale, units = integral units, logMap =
  unitLogHom), sourceLocalLogShellDatum_pStar, _preLogShell,
  _preLogShell_eq_range_unitLogHom, _logShell_eq_integralLogShell,
  _zero_mem_logShell, _unitLog_one_mem_logShell.

This file packages the actual local log-shell datum facts as one consumer for the genuine
common-prime-completion carrier.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddLocalLogShellDatumConsumerActual

open LeanFormal.IUT

universe u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]

/-- **PROVED consumer:** the actual local log-shell datum has scale `p* = logShellScale p`,
pre-log-shell = image of the integral unit log, log-shell = the actual integral log-shell,
and contains 0 and the log of 1. -/
theorem localLogShellDatum_consumer (place : FinitePlaceAtPrime K p) :
    (sourceLocalLogShellDatum (p := p) place).pStar = logShellScale p ∧
      (sourceLocalLogShellDatum (p := p) place).preLogShell =
        Set.range (fun u : (Integers (CommonPrimeCompletion place))ˣ =>
          unitLog (K := CommonPrimeCompletion place) u) ∧
        (sourceLocalLogShellDatum (p := p) place).logShell =
          (integralLogShell (K := CommonPrimeCompletion place) (p := p) :
            Set (CommonPrimeCompletion place)) ∧
          (0 : CommonPrimeCompletion place) ∈
            (sourceLocalLogShellDatum (p := p) place).logShell ∧
            unitLog (K := CommonPrimeCompletion place)
                (1 : (Integers (CommonPrimeCompletion place))ˣ) ∈
              (sourceLocalLogShellDatum (p := p) place).logShell :=
  ⟨sourceLocalLogShellDatum_pStar (p := p) place,
    sourceLocalLogShellDatum_preLogShell (p := p) place,
    sourceLocalLogShellDatum_logShell_eq_integralLogShell (p := p) place,
    sourceLocalLogShellDatum_zero_mem_logShell (p := p) place,
    sourceLocalLogShellDatum_unitLog_one_mem_logShell (p := p) place⟩

/-- Row record: reused local log-shell assets vs the consumer interface. -/
def localLogShellDatumRows : List (String × String × String) :=
  [ ("p* = logShellScale", "REUSED PROVED", "sourceLogShellStar_eq_logShellScale / sourceLocalLogShellDatum_pStar")
  , ("pre-log-shell = integral unit log image", "REUSED PROVED", "sourceLocalLogShellDatum_preLogShell(_eq_range_unitLogHom)")
  , ("log-shell = actual integralLogShell", "REUSED PROVED", "sourceLocalLogShellDatum_logShell_eq_integralLogShell")
  , ("zero/unit-log-one membership", "REUSED PROVED", "sourceLocalLogShellDatum_zero_mem_logShell / _unitLog_one_mem_logShell")
  , ("consumer bundle", "COMPOSED PROVED", "localLogShellDatum_consumer") ]

theorem localLogShellDatumRows_length : localLogShellDatumRows.length = 5 := rfl

#check localLogShellDatum_consumer
#check localLogShellDatumRows_length

end LeanFormal.IUT.XiFPaper.ShehddLocalLogShellDatumConsumerActual
end
