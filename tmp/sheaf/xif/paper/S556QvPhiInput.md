# S556: conditional actual Input(qvPhi R) reducing S548 data

Date: 2026-10-29. Naturality remains explicit; no fake divisor.

## Construction

S556InputDataActual K:
* ramification : RamificationIndexData K;
* valuationFamily : DvSmallValuationFamily K;
* divisor_naturality : for f : X -> Y and value,
    divisorAligned V X (L^x pullback f value)
    = (qvPhiRamificationModel R).gpPullback f (divisorAligned V Y value).

s556InputActual D : Input (qvPhiRamificationModel R):
  rationalFunctions := example32RationalFunctionsIso (S474, L^x inclusion)
  divisor X := example32DivisorAlignedS491 valuationFamily X
  divisor_natural := D.divisor_naturality.

s556FrobenioidPresentation builds the conditional FrobenioidPresentation.

S556DivisorNaturalityRequired R V is the exact remaining naturality statement
against the qvPhi ramification pullback.

## Reduction of S548

Compared with S548InputData, the arbitrary rationalFunctions and divisor are
replaced by:
* actual S474 L^x inclusion rational functions;
* actual S491 aligned valuation divisor.

Remaining parameters: ramification data R, valuation family V, and the
naturality hypothesis.

No fake divisor/naturality; no completion/L.
