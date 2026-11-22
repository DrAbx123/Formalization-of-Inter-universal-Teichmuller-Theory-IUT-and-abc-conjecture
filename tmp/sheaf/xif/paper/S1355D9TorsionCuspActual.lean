import tmp.sheaf.xif.paper.S1330CuspEpsilonActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31ArithmeticCompatibilitySlots

/-! # S1355: D9 torsion and cusp pairs from supplied D5/D8 data

Given a D5 torsion clause, the D9 torsion `(Prop, proof)` pair is actual.
Given a D9 cusp boundary origin, the D9 cusp pair is actual.  A D8
`SourceCuspClause` alone is not enough for the cusp pair: its exact first
field is `TorsionQuotientBoundaryOrigin`.  No D5/D8 clause is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1355D9TorsionCuspActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

universe u
variable {l : PrimeGeFive}

/-! ## 1. D9 torsion from a D5 clause -/

/-- The D9 torsion slot proposition.  It is the concrete slot statement of
`SourceDefinition31ArithmeticCompatibilitySlots`, not a replacement. -/
def S1355D9TorsionProp
    (T : SourceTorsionClause.{0, 0, 0} l) : Prop :=
  ArithmeticTorsionCompatibility T

/-- Given a D5 torsion clause, the D9 torsion pair is actual. -/
theorem S1355D9Torsion_proved
    (T : SourceTorsionClause.{0, 0, 0} l) :
    S1355D9TorsionProp T :=
  arithmeticTorsionCompatibility_of_clause T

/-- Exact first field of the D5 supply: the torsion clause itself. -/
abbrev S1355D5FirstField (l : PrimeGeFive) : Type 1 :=
  SourceTorsionClause.{0, 0, 0} l

/-! ## 2. D9 cusp from a boundary origin -/

/-- The D9 cusp slot proposition. -/
def S1355D9CuspProp
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (O : TorsionQuotientBoundaryOrigin l (S1280Arithmetic l) X) : Prop :=
  ArithmeticCuspOriginCompatibility O

/-- Given the cusp boundary origin, the D9 cusp pair is actual. -/
theorem S1355D9Cusp_proved
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (O : TorsionQuotientBoundaryOrigin l (S1280Arithmetic l) X) :
    S1355D9CuspProp O :=
  arithmeticCuspOriginCompatibility_of_supply O

/-- Exact first field of the D9 cusp slot over an actual K-core orbicurve. -/
abbrev S1355D9CuspFirstField
    (X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K) : Type 1 :=
  TorsionQuotientBoundaryOrigin l (S1280Arithmetic l) X

/-- A D8 cusp clause is the real-coordinate contract, not the boundary
origin; this records the type separation rather than a fake map. -/
abbrev S1355D8CuspField : Type := SourceCuspClause

end LeanFormal.IUT.XiFPaper.S1355D9TorsionCuspActual

end
