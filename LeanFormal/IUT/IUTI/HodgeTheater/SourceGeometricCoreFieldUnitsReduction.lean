/-
  Six-unit splitting of the source geometric core of Definition 3.1.

  Paper anchors (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Definition 3.1 (extraction lines 3123-3283).  Clause (a) (lines
    3127-3130) fixes the number field `F` and its algebraic closure; clause
    (b) (lines 3131-3157) makes `XF` a once-punctured elliptic curve of
    type (1,1) over `F`, and `XF -> CF` the stack-theoretic quotient of
    `XF` by the unique `F`-involution "-1" of `XF`; it also writes `Pi_X`,
    `Pi_C`, `Delta_X`, `Delta_C` with the natural exact sequences
    `1 -> Delta -> Pi -> GF -> 1` (lines 3158-3171).  Clause (d) (lines
    3185-3215) fixes `CK` of type (1,l-tors)^+- with K-core `CK = CF x_F K`
    and `XK` of type (1,l-tors) with the natural cartesian diagrams; clause
    (f) (line 3273) binds the cusp `epsilon` of `CK`.

  * The Lean record `SourceSignQuotientGeometricCore`
    (`SourceSignQuotientConstruction.lean:30-72`) carries the corresponding
    22 fields; report section 22.3 groups fields 3-22 into five cards
    (involution, sign action with quotient, group data, K-side, cusp).

  What this file proves (reduction pass; no instance is constructed):

  * Sections 1-2 freeze the 22 fields as the six carrier-parameterized
    units `SourceGeometricCore*Unit` together with the six propositions
    `SourceGeometricCore*Block = Nonempty (unit)`.  Every unit field is a
    verbatim copy of the core field group of the same name; nothing is
    added, weakened, or reordered, and each block is exactly the
    inhabitation statement of its field group.

  * Section 3 proves that the splitting is faithful: `toFieldUnits` and
    `sourceSignQuotientGeometricCoreOfFieldUnits` are mutually inverse at
    `rfl` level (the two-sided roundtrip conservation law), the `Nonempty`
    statements of core and bundle are equivalent, and the flat carrier
    chain base unit -> involution unit -> sign-quotient unit -> group-data
    unit -> K-side unit -> cusp unit shares all carriers
    (`nonempty_sourceSignQuotientGeometricCore_iff_unitChain`).  This is
    conditional assembly only: the core is built from a full bundle of
    units and nothing beyond the units is added.

  * Section 4 lifts the splitting to the consumer-level supplies:
    `SourceSignQuotientSupply`, `SourceSignQuotientGeometricCoreSupply`
    and the contract-root version are each equivalent to the corresponding
    six-unit supply, and the A2-gate transfer
    `sourceNativeArithmeticToSourceGate_of_units` is re-consumed in unit
    form.

  Boundary (explicit): no inhabitant of any unit is constructed in this
  file; the D6 orbicurve line (`SourceDefinition31OrbicurveInstance`) is
  not imported and not pre-empted; the degenerate point-fiber stack
  witness of `SourceEtaleStackInstanceSupplyReduction.lean` is not
  imported either, so the base unit stays a card here.  The place half of
  Definition 3.1 is untouched.

  Consumers: `SourceHodgeTheaterBridge`; `SourceOriginalInput.lean:39-43`;
  `SourceH1H2Construction.lean:273-279`; the D6 orbicurve line (interface
  via the six unit types and their block propositions).
-/

import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction
import Iut.Foundations.Orbicurve

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

noncomputable section

/-! ## 1. The six carrier-parameterized units of the geometric core -/

namespace InitialThetaSource

/-- Base unit, core fields 1-2: the curve `XF` and its once-punctured
binding (Definition 3.1(b), extraction lines 3131-3133).  Card in this
file; no inhabitant is constructed. -/
structure SourceGeometricCoreBaseUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) where
  xF : Iut.HyperbolicOrbicurve A.F
  xF_geometry : SourceOncePuncturedGeometry A.curve xF

/-- Involution unit, core fields 3-5: the unique `F`-involution "-1" of
`XF` with its square and uniqueness (Definition 3.1(b), extraction lines
3134-3137). -/
structure SourceGeometricCoreInvolutionUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (xF : Iut.HyperbolicOrbicurve A.F) where
  ellipticInvolution : xF.Hom xF
  ellipticInvolution_squared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id xF)
  unique_elliptic_involution :
    ∀ inv : xF.Hom xF,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id xF) →
      inv = ellipticInvolution

/-- Sign-quotient unit, core fields 6-10: the sign action, its inversion
identified with the parameter involution, the quotient curve `CF` and the
quotient witness (Definition 3.1(b), extraction lines 3134-3137: the
stack-theoretic quotient of `XF` by the unique `F`-involution). -/
structure SourceGeometricCoreSignQuotientUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (xF : Iut.HyperbolicOrbicurve A.F) (inv : xF.Hom xF) where
  signAction : Iut.OrbicurveSignAction xF
  signAction_inversion_eq : signAction.inversion = inv
  cF : Iut.HyperbolicOrbicurve A.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient

/-- Group-data unit, core fields 11-13: the `Pi_X`/`Pi_C` exact-sequence
data over the absolute Galois group and the compatible open immersions
(Definition 3.1(b), lines 3158-3171; (d), lines 3198-3211). -/
structure SourceGeometricCoreGroupUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (xF cF : Iut.HyperbolicOrbicurve A.F) where
  xFGroups : SourceOrbicurveGroupData xF (Iut.AbsoluteGaloisProfinite A.F)
  cFGroups : SourceOrbicurveGroupData cF (Iut.AbsoluteGaloisProfinite A.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.F)
    xFGroups.sequence cFGroups.sequence

/-- K-side unit, core fields 14-21: `CK` of type (1,l-tors)^+-, `XK` of
type (1,l-tors), the scalar extensions to `K` and the defining equations
`XK = xKExtension.result`, `CK = cKExtension.result` (Definition 3.1(d),
extraction lines 3185-3192). -/
structure SourceGeometricCoreKSideUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (xF cF : Iut.HyperbolicOrbicurve A.F) where
  xK : Iut.HyperbolicOrbicurve A.K
  cK : Iut.HyperbolicOrbicurve A.K
  xKExtension : SourceOrbicurveScalarExtension A.F A.K xF
  cKExtension : SourceOrbicurveScalarExtension A.F A.K cF
  xKType : xK.signature = sourceTypeOneLTorsion l
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result

/-- Cusp unit, core field 22: the boundary cusp `epsilon` of `CK`
(Definition 3.1(f), extraction line 3273). -/
structure SourceGeometricCoreCuspUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (cK : Iut.HyperbolicOrbicurve A.K) where
  epsilon : Iut.OrbicurveBoundaryCusp cK
/-! ## 2. The six freeze propositions and the core projections -/

/-- Freeze of the base unit: the curve-and-binding pair exists. -/
def SourceGeometricCoreBaseBlock {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l) : Prop :=
  Nonempty (SourceGeometricCoreBaseUnit A)

/-- Freeze of the involution unit at a fixed curve. -/
def SourceGeometricCoreInvolutionBlock {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l)
    (xF : Iut.HyperbolicOrbicurve A.F) : Prop :=
  Nonempty (SourceGeometricCoreInvolutionUnit A xF)

/-- Freeze of the sign-quotient unit at a fixed curve and involution. -/
def SourceGeometricCoreSignQuotientBlock {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l)
    (xF : Iut.HyperbolicOrbicurve A.F) (inv : xF.Hom xF) : Prop :=
  Nonempty (SourceGeometricCoreSignQuotientUnit A xF inv)

/-- Freeze of the group-data unit at fixed curves `xF`, `cF`. -/
def SourceGeometricCoreGroupBlock {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l)
    (xF cF : Iut.HyperbolicOrbicurve A.F) : Prop :=
  Nonempty (SourceGeometricCoreGroupUnit A xF cF)

/-- Freeze of the K-side unit at fixed curves `xF`, `cF`. -/
def SourceGeometricCoreKSideBlock {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l)
    (xF cF : Iut.HyperbolicOrbicurve A.F) : Prop :=
  Nonempty (SourceGeometricCoreKSideUnit A xF cF)

/-- Freeze of the cusp unit at a fixed K-side curve `cK`. -/
def SourceGeometricCoreCuspBlock {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l)
    (cK : Iut.HyperbolicOrbicurve A.K) : Prop :=
  Nonempty (SourceGeometricCoreCuspUnit A cK)

/-- Any geometric core projects to the base block (fields 1-2). -/
theorem sourceSignQuotientGeometricCore_baseBlock
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    SourceGeometricCoreBaseBlock A :=
  ⟨⟨G.xF, G.xF_geometry⟩⟩

/-- Any geometric core projects to the involution block (fields 3-5). -/
theorem sourceSignQuotientGeometricCore_involutionBlock
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    SourceGeometricCoreInvolutionBlock A G.xF :=
  ⟨⟨G.ellipticInvolution, G.ellipticInvolution_squared,
    G.unique_elliptic_involution⟩⟩

/-- Any geometric core projects to the sign-quotient block (fields 6-10). -/
theorem sourceSignQuotientGeometricCore_signQuotientBlock
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    SourceGeometricCoreSignQuotientBlock A G.xF G.ellipticInvolution :=
  ⟨⟨G.signAction, G.signAction_inversion_eq_ellipticInvolution, G.cF,
    G.quotient, G.quotientWitness⟩⟩

/-- Any geometric core projects to the group-data block (fields 11-13). -/
theorem sourceSignQuotientGeometricCore_groupBlock
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    SourceGeometricCoreGroupBlock A G.xF G.cF :=
  ⟨⟨G.xFGroups, G.cFGroups, G.fGroupInclusion⟩⟩

/-- Any geometric core projects to the K-side block (fields 14-21). -/
theorem sourceSignQuotientGeometricCore_kSideBlock
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    SourceGeometricCoreKSideBlock A G.xF G.cF :=
  ⟨⟨G.xK, G.cK, G.xKExtension, G.cKExtension, G.xKType, G.cKType,
    G.xK_eq_extension, G.cK_eq_extension⟩⟩

/-- Any geometric core projects to the cusp block (field 22). -/
theorem sourceSignQuotientGeometricCore_cuspBlock
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    SourceGeometricCoreCuspBlock A G.cK :=
  ⟨⟨G.epsilon⟩⟩

/-! ## 3. The bundle, the splitting, and the carrier chain -/

/-- The six units assembled along the field dependency chain
`xF -> (involution) -> (sign action, CF) -> (K-side) -> cusp`. -/
structure SourceGeometricCoreFieldUnits
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) where
  base : SourceGeometricCoreBaseUnit A
  involution : SourceGeometricCoreInvolutionUnit A base.xF
  signQuotient :
    SourceGeometricCoreSignQuotientUnit A base.xF involution.ellipticInvolution
  groups : SourceGeometricCoreGroupUnit A base.xF signQuotient.cF
  kSide : SourceGeometricCoreKSideUnit A base.xF signQuotient.cF
  cusp : SourceGeometricCoreCuspUnit A kSide.cK

namespace SourceSignQuotientGeometricCore

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}

/-- Split a geometric core into the six units; fields are copied verbatim. -/
def toFieldUnits (G : SourceSignQuotientGeometricCore A) :
    SourceGeometricCoreFieldUnits A where
  base := ⟨G.xF, G.xF_geometry⟩
  involution :=
    ⟨G.ellipticInvolution, G.ellipticInvolution_squared,
      G.unique_elliptic_involution⟩
  signQuotient :=
    ⟨G.signAction, G.signAction_inversion_eq_ellipticInvolution, G.cF,
      G.quotient, G.quotientWitness⟩
  groups := ⟨G.xFGroups, G.cFGroups, G.fGroupInclusion⟩
  kSide :=
    ⟨G.xK, G.cK, G.xKExtension, G.cKExtension, G.xKType, G.cKType,
      G.xK_eq_extension, G.cK_eq_extension⟩
  cusp := ⟨G.epsilon⟩

end SourceSignQuotientGeometricCore

/-- Assemble the core from a full bundle of units (conditional assembly;
nothing beyond the units is added). -/
def sourceSignQuotientGeometricCoreOfFieldUnits
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (U : SourceGeometricCoreFieldUnits A) :
    SourceSignQuotientGeometricCore A where
  xF := U.base.xF
  xF_geometry := U.base.xF_geometry
  ellipticInvolution := U.involution.ellipticInvolution
  ellipticInvolution_squared := U.involution.ellipticInvolution_squared
  unique_elliptic_involution := U.involution.unique_elliptic_involution
  signAction := U.signQuotient.signAction
  signAction_inversion_eq_ellipticInvolution :=
    U.signQuotient.signAction_inversion_eq
  cF := U.signQuotient.cF
  quotient := U.signQuotient.quotient
  quotientWitness := U.signQuotient.quotientWitness
  xFGroups := U.groups.xFGroups
  cFGroups := U.groups.cFGroups
  fGroupInclusion := U.groups.fGroupInclusion
  xK := U.kSide.xK
  cK := U.kSide.cK
  xKExtension := U.kSide.xKExtension
  cKExtension := U.kSide.cKExtension
  xKType := U.kSide.xKType
  cKType := U.kSide.cKType
  xK_eq_extension := U.kSide.xK_eq_extension
  cK_eq_extension := U.kSide.cK_eq_extension
  epsilon := U.cusp.epsilon

/-- Conservation law: splitting and reassembling a geometric core returns
the same core. -/
@[simp] theorem sourceSignQuotientGeometricCoreOfFieldUnits_toFieldUnits
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    sourceSignQuotientGeometricCoreOfFieldUnits G.toFieldUnits = G :=
  rfl

/-- Conservation law: assembling and splitting a unit bundle returns the
same bundle. -/
@[simp] theorem toFieldUnits_sourceSignQuotientGeometricCoreOfFieldUnits
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (U : SourceGeometricCoreFieldUnits A) :
    (sourceSignQuotientGeometricCoreOfFieldUnits U).toFieldUnits = U :=
  rfl

/-- The splitting is an equivalence of inhabitation. -/
theorem nonempty_sourceSignQuotientGeometricCore_iff_fieldUnits
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) :
    Nonempty (SourceSignQuotientGeometricCore A) ↔
      Nonempty (SourceGeometricCoreFieldUnits A) :=
  ⟨fun h => ⟨h.some.toFieldUnits⟩,
    fun h => ⟨sourceSignQuotientGeometricCoreOfFieldUnits h.some⟩⟩

/-- Flat carrier-chain form of the decomposition: a core exists exactly
when the six units exist with shared carriers along the dependency chain. -/
theorem nonempty_sourceSignQuotientGeometricCore_iff_unitChain
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) :
    Nonempty (SourceSignQuotientGeometricCore A) ↔
      ∃ (B : SourceGeometricCoreBaseUnit A)
        (I : SourceGeometricCoreInvolutionUnit A B.xF)
        (Q : SourceGeometricCoreSignQuotientUnit A B.xF I.ellipticInvolution)
        (D : SourceGeometricCoreGroupUnit A B.xF Q.cF)
        (K : SourceGeometricCoreKSideUnit A B.xF Q.cF),
        Nonempty (SourceGeometricCoreCuspUnit A K.cK) := by
  constructor
  · rintro ⟨G⟩
    exact ⟨G.toFieldUnits.base, G.toFieldUnits.involution,
      G.toFieldUnits.signQuotient, G.toFieldUnits.groups,
      G.toFieldUnits.kSide, ⟨G.toFieldUnits.cusp⟩⟩
  · rintro ⟨B, I, Q, D, K, ⟨E⟩⟩
    exact ⟨sourceSignQuotientGeometricCoreOfFieldUnits ⟨B, I, Q, D, K, E⟩⟩
end InitialThetaSource

/-! ## 4. Supply-level and consumer interfaces -/

/-- Six-unit supply over every arithmetic datum. -/
def SourceGeometricCoreFieldUnitsSupply (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty (SourceGeometricCoreFieldUnits A)

/-- Six-unit supply over the arithmetic roots of Definition 3.1 contracts. -/
def SourceGeometricCoreFieldUnitsSupplyAtContractRoots
    (l : PrimeGeFive) : Prop :=
  ∀ S : SourceDefinition31Data.{u} l,
    Nonempty (SourceGeometricCoreFieldUnits S.arithmetic)

/-- Geometric-core supply is exactly six-unit supply. -/
theorem sourceSignQuotientGeometricCoreSupply_iff_fieldUnitsSupply :
    SourceSignQuotientGeometricCoreSupply.{u} l ↔
      SourceGeometricCoreFieldUnitsSupply.{u} l := by
  constructor
  · intro h A
    exact (nonempty_sourceSignQuotientGeometricCore_iff_fieldUnits A).mp (h A)
  · intro h A
    exact (nonempty_sourceSignQuotientGeometricCore_iff_fieldUnits A).mpr (h A)

/-- Full sign-quotient supply is exactly six-unit supply (the place half is
unconditional, `SourceDefinition31SignQuotientSupplyReduction.lean:226`). -/
theorem sourceSignQuotientSupply_iff_fieldUnitsSupply :
    SourceSignQuotientSupply.{u} l ↔
      SourceGeometricCoreFieldUnitsSupply.{u} l :=
  (sourceSignQuotientSupply_iff_geometricCoreSupply (l := l)).trans
    (sourceSignQuotientGeometricCoreSupply_iff_fieldUnitsSupply (l := l))

/-- Contract-root sign-quotient supply is exactly six-unit supply at
contract roots. -/
theorem contractRootSignQuotientSupply_iff_fieldUnitsSupplyAtContractRoots :
    ContractRootSignQuotientSupply.{u} l ↔
      SourceGeometricCoreFieldUnitsSupplyAtContractRoots.{u} l :=
  (contractRootSignQuotientSupply_iff_geometricCoreSupplyAtContractRoots
      (l := l)).trans
    ⟨fun h S =>
      (nonempty_sourceSignQuotientGeometricCore_iff_fieldUnits S.arithmetic).mp
        (h S),
     fun h S =>
      (nonempty_sourceSignQuotientGeometricCore_iff_fieldUnits S.arithmetic).mpr
        (h S)⟩

/-- A2-gate transfer in unit form: the gate follows from six-unit supply
and clause-assembly supply. -/
theorem sourceNativeArithmeticToSourceGate_of_fieldUnits
    (hU : SourceGeometricCoreFieldUnitsSupply.{u} l)
    (hA : SourceClauseAssemblySupply.{u} l) :
    SourceNativeArithmeticToSourceGate.{u} l :=
  sourceNativeArithmeticToSourceGate_of_units
    ((sourceSignQuotientGeometricCoreSupply_iff_fieldUnitsSupply
        (l := l)).mpr hU) hA

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def definition31GeometricCoreFieldUnitsReduction : Obligation :=
  { id := "IUT-I.definition-3.1-geometric-core-field-units-reduction"
    source :=
      "IUT I, Definition 3.1(a)-(f); extraction lines 3123-3283"
    status := VerificationStatus.interface
    note :=
      "Six-unit splitting of the 22-field geometric core " ++
        "(SourceSignQuotientConstruction.lean:30-72). Proved: the core is " ++
        "carrier-isomorphic to the six-unit bundle (base, involution, sign " ++
        "quotient, group data, K-side, cusp), with an rfl-level two-sided " ++
        "roundtrip, an inhabitation equivalence and a flat carrier-chain " ++
        "form; SourceSignQuotientSupply, " ++
        "SourceSignQuotientGeometricCoreSupply and the contract-root " ++
        "versions are each equivalent to the corresponding six-unit " ++
        "supply; the A2-gate transfer is re-consumed in unit form.  No " ++
        "inhabitant of the units is constructed here (D6 line); the " ++
        "degenerate point-fiber witness of " ++
        "SourceEtaleStackInstanceSupplyReduction.lean is not imported.  " ++
        "Consumers: SourceHodgeTheaterBridge, SourceOriginalInput.lean:39-43, " ++
        "SourceH1H2Construction.lean:273-279."
    dependsOn :=
      [ "IUT-I.definition-3.1-sign-quotient-supply-reduction" ] }

end LeanFormal.IUT.Audit
