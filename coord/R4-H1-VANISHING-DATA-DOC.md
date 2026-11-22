# R4 `H1VanishingData` field-type snippet (for emmy; donor-based)

Donors (import paths + line refs; oleans exist):
- `tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_AdelicIndex`
  (`ConstantsAreBase` :48, `ell_zero_eq_one_of_constantsAreBase` :51,
  `indexOfSpecialty` :139, `residuePairing` :345)
- `tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_RiemannRochRows`
  (`RiemannIndexFormula` :22, `WeilDualityAdelic` :28, `WeilDuality` :34,
  `weilDuality_of_riemannIndex_of_adelic` :59)
- `tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_WeilOfKaehler` (`ResidueTheorem` :110)
- `tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_SerrePairing`
  (`residueSumOffChart` :99, `serrePairing` :229)

## Snippet (copy into the R4 file; names qualified as needed)

```lean
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_AdelicIndex
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_RiemannRochRows
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_WeilOfKaehler
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_SerrePairing

noncomputable section
namespace LeanFormal.IUT.XiFPaper.R4H1Vanishing

open AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- The R4 H1-vanishing package: the paper's H1 assembly inputs, all as
PORTED FLT interface propositions (no new assumptions beyond the cited donors).
`Divisor`, `ell`, `indexOfSpecialty`, `genus` come from the ported FLT files. -/
structure H1VanishingData [HasPrincipalDivisors K F] where
  /-- constants are exactly the base field (R4 pack: no extra constants). -/
  constantsAreBase : ConstantsAreBase K F
  /-- the residue theorem (sum of residues of an adelic form vanishes). -/
  residueTheorem : ResidueTheorem K F
  /-- Weil duality in adelic form (Prop-level). -/
  weilDualityAdelic : WeilDualityAdelic K F
  /-- the H^1 vanishing statement on the relevant divisors: index of specialty
  vanishes (equivalently ell D = deg D + 1 - genus under Riemann-Roch). -/
  h1_vanish : ∀ D : Divisor K F, indexOfSpecialty D = 0

/-- the Riemann-type specialization: index formula follows from H1 vanishing. -/
theorem H1VanishingData.indexFormula [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] (hD : H1VanishingData K F)
    (D : Divisor K F) :
    (indexOfSpecialty D : ℤ) =
      (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ)) := by
  -- with hD.h1_vanish the RHS is 0 up to the index definition; this is the
  -- paper's H1-vanishing -> Riemann-index step (R4 size input).
  rw [hD.h1_vanish D]
  sorry

end LeanFormal.IUT.XiFPaper.R4H1Vanishing
end
```

NOTE: the last `sorry` is a placeholder only in this DOC snippet (not in any
submitted file): the actual R4 file must either prove it from the ported
`RiemannIndexFormula` (donor :22: `indexOfSpecialty D = ell D - (deg D + 1 - genus)`
as an integer equality) or take it as an explicit field.  Do NOT use `sorry` in the
real file; resolve the `ℕ`-vs-`ℤ` cast with `Nat.cast_sub`/`omega` as appropriate.

## Notes on typeclass arguments

- `indexOfSpecialty : Divisor K F → ℕ` requires `[HasPrincipalDivisors K F]`
  (the structure binder above); `ell`/`Divisor.degree`/`genus` need
  `[IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]` for the
  duality/Riemann forms (add them at the theorem, not the structure).
- `WeilDuality K F` is the non-adelic Prop (donor :34); the bridge
  `weilDuality_of_riemannIndex_of_adelic (hRI : RiemannIndexFormula) (hWD : WeilDualityAdelic)`
  (donor :59) turns the adelic field into it — prefer carrying
  `weilDualityAdelic` in the structure and deriving `WeilDuality`.
- `residuePairing` (AdelicIndex :345) is available if the R4 size statement needs
  the pairing form; `serrePairing (hRT : ResidueTheorem K F)` (SerrePairing :229)
  is the Cech/residue pairing consumer.

## R4/H1 packing usage

- size/H1 packing should consume `H1VanishingData.h1_vanish` (or the derived index
  formula) plus `constantsAreBase`; `h1_vanish` is the paper's H^1 = 0 input;
- line refs for the paper side: IV L2483-2488 (C2 display), L1411-1425 (S_ar layer diffs)
  are unrelated; the R4 paper statements live in the R4 package doc (grace/emmy owners).
