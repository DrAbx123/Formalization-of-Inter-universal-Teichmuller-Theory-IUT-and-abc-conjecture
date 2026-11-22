/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.SourceEtaleStackInstanceSupplyReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.Tactic

/-! # A2 geometric core: the constructible `xF` / `xF_geometry` part

`SourceSignQuotientData A` (the A2 first field) has first fields
`xF : Iut.HyperbolicOrbicurve A.F` and
`xF_geometry : SourceOncePuncturedGeometry A.curve xF`.  These two ARE
constructible from the existing one-point etale-stack fiber via
`realizedHyperbolicOrbicurve` (degenerate witness: the signature is inserted,
no geometric content).  The remaining ~20 fields (elliptic involution and its
uniqueness, sign action/quotient, group data, scalar extensions, type
equations, boundary cusp, ...) remain the A2 source-geometry card.

No inhabitant of the full `SourceSignQuotientData` is asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A2GeometricCorePartialActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

variable {l : PrimeGeFive}

/-- The degenerate actual `xF` from the source point etale-stack fiber. -/
noncomputable def xFOfStackPoint
    (A : InitialThetaArithmeticData.{0} l) : Iut.HyperbolicOrbicurve A.F :=
  realizedHyperbolicOrbicurve A.F (sourceStackPointEtaleFiber A.F)
    (sourceStackPointEtaleFiber_isStack A.F)
    InitialThetaSource.sourceTypeOneOne
    InitialThetaSource.sourceTypeOneOne_hyperbolic

/-- The `xF_geometry` certificate for the degenerate `xF`. -/
theorem xFOfStackPoint_geometry
    (A : InitialThetaArithmeticData.{0} l) :
    Nonempty (InitialThetaSource.SourceOncePuncturedGeometry A.curve (xFOfStackPoint A)) :=
  ⟨⟨rfl⟩⟩

/-- The exact statement: the first two fields of `SourceSignQuotientData` are
constructible (degenerately). -/
theorem exists_xF_xF_geometry
    (A : InitialThetaArithmeticData.{0} l) :
    ∃ XF : Iut.HyperbolicOrbicurve A.F,
      Nonempty (InitialThetaSource.SourceOncePuncturedGeometry A.curve XF) :=
  exists_sourceOncePuncturedGeometry_of_sourceStackPoint A

/-- The first remaining field of the full A2 structure (explicit source card):
`ellipticInvolution : xF.Hom xF` together with its square/id and uniqueness.
The full `SourceSignQuotientData` still has no inhabitant. -/
def a2FirstRemainingFields : List String :=
  [ "ellipticInvolution : xF.Hom xF"
    , "ellipticInvolution_squared : comp inv inv ~ id"
    , "unique_elliptic_involution"
    , "signAction : OrbicurveSignAction xF + inversion_eq"
    , "cF / quotient / quotientWitness"
    , "xFGroups / cFGroups / fGroupInclusion"
    , "xK / cK / xKExtension / cKExtension / type equations"
    , "V (Definition 3.1(e)-(f) tuple components)" ]

theorem a2FirstRemainingFields_length : a2FirstRemainingFields.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2GeometricCorePartialActual

end