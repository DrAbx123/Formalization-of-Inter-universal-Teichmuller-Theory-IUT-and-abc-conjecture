# S561: minimal S556InputDataActual package

Date: 2026-10-29. Naturality remains the only gap.

## Package

S561MinimalPackage K:
* ramification : RamificationIndexData K;
* valuation : DvSmallValuationFamily K;
* naturality : S556DivisorNaturalityRequired R V.

s561InputData P: builds S556InputDataActual from the package.
s561Input P: s556InputActual of that data, i.e. actual Input(qvPhi R).

## Field equalities

s561Input_rationalFunctions:
  (s561Input P).rationalFunctions = example32RationalFunctionsIso (S474).

s561Input_divisor:
  (s561Input P).divisor = fun X => example32DivisorAlignedS491 P.valuation X.

Both are rfl.

## Exact gap

S561NaturalityGap R V := S556DivisorNaturalityRequired R V.
Naturality of the aligned valuation divisor against the qvPhi ramification
pullback is the only remaining datum; R and V are explicit parameters.

No fake naturality/divisor; no completion/L.
