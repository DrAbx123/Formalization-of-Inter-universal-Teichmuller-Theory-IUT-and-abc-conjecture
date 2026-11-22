import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31ArithmeticCompatibilitySlots

/-! # S1339: D9 compatibility — actual section pair and exact first fields

Five D9 slots are opaque `(Prop, proof)` pairs in `SourceDefinition31Data`.
This file constructs the one slot whose statement is already an actual
consequence of the S1280 place selection: the sections slot.  The other
four slots are recorded as exact first fields; no D5-D8 clause is supplied.
No `True`/PUnit substitution is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1339D9CompatibilityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u
variable {l : PrimeGeFive}

section Sections

/-- The D9 sections slot at the actual S1280 place selection.  This is the
paper's Definition 3.1(e) section condition, not a replacement proposition. -/
def S1339D9SectionsProp : Prop :=
  ArithmeticSectionCompatibility (S1280Selection l)

/-- Actual proof of the D9 sections slot from the S1280 selection. -/
theorem S1339D9Sections_proved :
    S1339D9SectionsProp (l := l) :=
  arithmeticSectionCompatibility_canonical (S1280Selection l)

end Sections

/-! ## Exact first fields of the other four D9 slots -/

/-- Reduction slot: the first missing field is the clause-(c) coprimality
card.  Even the reduction cards S1280 are actual, but the bad-residue
coproprimility card is not. -/
abbrev S1339D9ReductionFirstField (l : PrimeGeFive) : Type :=
  BadPlaceQParameterCards (S1280Selection l)

/-- At l = 5 the actual S1280 bad place has residue characteristic 5, so the
reduction slot's first field is impossible for that selection. -/
theorem S1339D9ReductionFirstField_impossible_at_five :
    ¬ Nonempty (S1339D9ReductionFirstField S1280Five) := by
  simpa [S1339D9ReductionFirstField] using
    S1280_clauseC_refuted_at_five

/-- Torsion slot: first field is the D5 torsion clause itself; the actual
rank-two basis is missing (S1298). -/
abbrev S1339D9TorsionFirstField (l : PrimeGeFive) : Type 1 :=
  SourceTorsionClause.{0, 0, 0} l

/-- Orbicurve slot: the actual K-core orbicurve object is not supplied by
the compiled source; the slot's first field is that source object, not a
signature or an empty clause. -/
abbrev S1339D9OrbicurveFirstField : Type 1 :=
  Iut.HyperbolicOrbicurve (S1280Arithmetic l).K

/-- Cusp slot: first field is the boundary-origin datum over an actual K-core
orbicurve.  S1320 supplies the cusp point but not this origin datum. -/
abbrev S1339D9CuspFirstField
    (X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K) : Type 1 :=
  TorsionQuotientBoundaryOrigin l (S1280Arithmetic l) X

end LeanFormal.IUT.XiFPaper.S1339D9CompatibilityActual

end
