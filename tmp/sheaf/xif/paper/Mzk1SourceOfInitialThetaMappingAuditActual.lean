/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A742: reverse mapping audit — lana InitialThetaData D vs our SourceNativeInitialThetaData T -/

/- Our T (`SourceDefinition31Quantifiers.lean:1681`):
* arithmetic : InitialThetaArithmeticData l = {Fmod, F, K (NumberField each), tower,
  curve : PuncturedEllipticCurve F} (ArithmeticData.lean:62-81);
* tuple : SourceInitialThetaTuple arithmetic -> contains `source : SourceSignQuotientData A`
  (the source-side V/V_mod^bad/sign-quotient data S);
* clauseA : SourceClauseA A S (`:889`) = stable reduction at every finite place p of A.F,
  field_of_moduli, maximal solvable extension/property/contains;
* clauseB : (`:959`) = multiplicative reduction over V_mod^bad + SourceTateComparisonWitness;
* clauseC : (`:1007`) = torsion23 rational, torsion basis (Fin 2 -> ZMod l) ~ LTorsion l,
  K/F carrier comparison;
* clauseD : (`:1106`) = orbicurve sign action/quotient/witness + scalar extension;
* clauseE : (`:1432`) = V = V_section.selected, selected_equiv (NumberFieldPlace A.Fmod ~ {v in V});
* clauseF : (`:1543`) = TorsionQuotientBoundaryOrigin l A S.cK.

## Reverse map (lana D -> our fields)
| our field | source in lana D | status |
| A.F | D.F (NumberField) | DIRECT |
| A.Fmod | `fieldOfModuli D.F D.E` (derived) | DERIVED (type is a field; our A.Fmod is a structure field, need instance transfer) |
| A.K | D.prime.torsionField (IntermediateField D.F D.Fbar) as a NumberField type | PLAUSIBLE (instance transfer FiniteDimensional/IsGalois) |
| A.curve | D.E plus once-puncture = D.X | DIRECT-ish (WeierstrassCurve + IsElliptic from D.isElliptic) |
| A.tower : ThetaFieldTower l Fmod F K | needs sqrt(-1)/Galois/finite-dim/coprime l: lana global/prime provide the arithmetic hypotheses but the record is ours | NEEDS CONSTRUCTION |
| S : SourceSignQuotientData A | lana D.localData / D.orb provide V, V_mod^bad, orbicurve data, but the source-sign-quotient record is ours and has different shape | NEEDS CONSTRUCTION |
| clauseA | D.global (stable reduction/field of moduli/max-solvable) | NEEDS TRANSLATION |
| clauseB | D.global + D.localData (multiplicative reduction, Tate) | NEEDS TRANSLATION |
| clauseC | D.prime (mod-l rep, torsion field, basis) | PLAUSIBLE with construction |
| clauseD | D.orb (orbicurve data, sign action?) | NEEDS TRANSLATION |
| clauseE | D.localData (valuation section V) | NEEDS TRANSLATION |
| clauseF | D.localData (torsion quotient boundary) | NEEDS TRANSLATION |

## Conclusion (A742)
The reverse map is NOT yet available: 3 fields map directly/derived (F, Fmod, curve), 2 are plausible
with instance transfer (K, clauseC), and the remaining 7 need new construction/translation layers
(tower, S, clauses A,B,D,E,F).  In particular the source-side record `SourceSignQuotientData A` has
no counterpart in lana D and must be constructed from D.localData/D.orb before clauses can be
proved.  Hence our 3.12 does NOT yet cover an arbitrary lana InitialThetaData D; the minimal next
constructions are: (i) A from (D.F, fieldOfModuli, torsionField, E); (ii) S from D.localData/orb;
(iii) six clause translations.  Nothing is assumed as an axiom; no fake definition is introduced. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SourceOfInitialThetaMappingAuditActual

/-- Reverse-mapping rows: (our field, lana source, status). -/
def sourceOfInitialThetaRows : List (String × String × String) :=
  [ ("A.F", "D.F", "DIRECT"),
    ("A.Fmod", "fieldOfModuli D.F D.E", "DERIVED/transfer"),
    ("A.curve", "D.E + once-puncture", "DIRECT-ish"),
    ("A.K", "D.prime.torsionField", "PLAUSIBLE/transfer"),
    ("A.tower", "global/prime hypotheses -> ThetaFieldTower", "NEEDS CONSTRUCTION"),
    ("S : SourceSignQuotientData", "D.localData + D.orb", "NEEDS CONSTRUCTION"),
    ("clauseA", "D.global", "NEEDS TRANSLATION"),
    ("clauseB", "D.global + D.localData", "NEEDS TRANSLATION"),
    ("clauseC", "D.prime", "PLAUSIBLE"),
    ("clauseD", "D.orb", "NEEDS TRANSLATION"),
    ("clauseE", "D.localData", "NEEDS TRANSLATION"),
    ("clauseF", "D.localData", "NEEDS TRANSLATION") ]

theorem sourceOfInitialThetaRows_length : sourceOfInitialThetaRows.length = 12 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SourceOfInitialThetaMappingAuditActual
