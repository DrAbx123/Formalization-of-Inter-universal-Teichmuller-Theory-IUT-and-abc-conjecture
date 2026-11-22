/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A740: mapping audit — our SourceNativeInitialThetaData T vs lana InitialThetaData -/

/- Field inventories (read-only):
* our T (`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1681`):
  arithmetic : InitialThetaArithmeticData l; tuple; clauses A-F.
  `InitialThetaArithmeticData` (`ArithmeticData.lean:62-81`): Fmod, F (NumberField),
  K (NumberField), algebra/tower/Galois/finite-dim fields, `curve : PuncturedEllipticCurve F`.
  `PuncturedEllipticCurve F` (`Foundations/Geometry/PuncturedEllipticCurve.lean:17`):
  `curve : WeierstrassCurve F`, `isElliptic : curve.IsElliptic`, `puncture : Point`.
* lana InitialThetaData (`Iut/Cor312/ThetaData/Basic.lean:81-113`) fields:
  F (Field, NumberField), Fbar (Field, Algebra F Fbar, IsAlgClosure F Fbar),
  E : WeierstrassCurve F (IsElliptic), VBad : Set (FinitePlace (fieldOfModuli F E)),
  global : IsInitialThetaGlobalData F E Fbar VBad,
  prime : AdmissiblePrimeData F E Fbar VBad,
  orb : OrbicurveData F E Fbar VBad prime,
  localData : LocalThetaData F E Fbar VBad prime orb.

## Mapping table (status: direct / constructible / needs construction / missing)
| lana field | our source | status |
| F | T.arithmetic.F (NumberField instance present) | DIRECT |
| Fbar | not a field of T; use Mathlib `AlgebraicClosure T.arithmetic.F` (Field/Algebra/IsAlgClosure instances available) | CONSTRUCTIBLE (canonical choice; needs universe check) |
| E | T.arithmetic.curve.curve : WeierstrassCurve F; T.arithmetic.curve.isElliptic gives IsElliptic | DIRECT |
| VBad | no set of FinitePlace of the moduli field in T; clauses A/B encode bad-reduction predicates, not this set | NEEDS CONSTRUCTION (FinitePlace set of fieldOfModuli F E + reduction data) |
| global : IsInitialThetaGlobalData | our clauses A-F are source-shape predicates; no constructor to lana's structure | NEEDS CONSTRUCTION (translation clauses A-F -> lana global fields) |
| prime : AdmissiblePrimeData | l = ℓ and our `SourceTorsionTransport`/`SourcePlaceSelection`/`SourceTorsionRankOneQuotient` modules provide mod-ℓ representation/torsion data candidates | PLAUSIBLE with construction (build AdmissiblePrimeData from torsion/tower data) |
| orb : OrbicurveData | our `Iut.OrbicurveFundamentalGroupData` (SourceDefinition31Quantifiers.lean:32) and once-punctured orbicurve primitives exist (Foundations/Oka orbicurve base) | PLAUSIBLE with construction (bundle existing primitives into lana OrbicurveData) |
| localData : LocalThetaData | our LocalReduction/TatePointQuotientBoundary modules (imported by the source file) provide local reduction/Tate data candidates | PLAUSIBLE with construction (wrap into LocalThetaData) |

## Conclusion (A740)
2/8 fields map directly (F, E); 1 constructible (Fbar via AlgebraicClosure); 3 plausible with explicit
construction (prime, orb, localData, whose raw materials exist in our repo); 2 hard (VBad set of
finite places of the moduli field, and the global-data structure translation from clauses A-F).
Hence a full `initialThetaDataOfSource` is NOT yet available; the honest executable plan is
`initialThetaDataOfSource (T) (Fbar := AlgebraicClosure ..) (VBad) (global) (prime) (orb)
(localData)` with the 4 constructions above, of which VBad/global need new mathematical work.
Nothing here is assumed as axiom; no lana construction is faked. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataMappingAuditActual

/-- Mapping rows: (lana field, our source, status). -/
def initialThetaMappingRows : List (String × String × String) :=
  [ ("F", "T.arithmetic.F (NumberField)", "DIRECT"),
    ("E", "T.arithmetic.curve.curve + isElliptic", "DIRECT"),
    ("Fbar", "AlgebraicClosure T.arithmetic.F", "CONSTRUCTIBLE"),
    ("VBad", "FinitePlace set of fieldOfModuli F E + reduction data", "NEEDS CONSTRUCTION"),
    ("global", "clauses A-F -> IsInitialThetaGlobalData", "NEEDS CONSTRUCTION"),
    ("prime", "SourceTorsionTransport/PlaceSelection/RankOneQuotient -> AdmissiblePrimeData", "PLAUSIBLE"),
    ("orb", "OrbicurveFundamentalGroupData -> OrbicurveData", "PLAUSIBLE"),
    ("localData", "LocalReduction/TatePointQuotientBoundary -> LocalThetaData", "PLAUSIBLE") ]

theorem initialThetaMappingRows_length : initialThetaMappingRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataMappingAuditActual
