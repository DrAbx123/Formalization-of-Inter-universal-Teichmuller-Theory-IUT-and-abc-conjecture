/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ShellVolumeUpperBoundLanaActual
import tmp.external.ported.lana.Iut.Concrete.ThetaRegion
import tmp.external.ported.lana.Iut.Concrete.Invariants

/-! # A727 hull: concrete lana instance for the (U) consumer

Location of the concrete lana data (only-read from the ported tree):

* `Iut.concreteVariantData (D : InitialThetaData.{u}) : Corollary312VariantData.{u}`
  (`Iut/Concrete/ThetaRegion.lean:359`);
* `Iut.InitialThetaData.invariants (D) : Theorem110Invariants (concreteVariantData D)`
  (`Iut/Concrete/Invariants.lean:262`), used as `D.invariants`;
* `Iut.TowerArithmetic (D) : Prop` (`Iut/Concrete/Invariants.lean:287`) and
  `Iut.TowerArithmetic.localEstimate (TA : TowerArithmetic D) : (D.invariants).LocalEstimate`
  (`Iut/Concrete/LocalEstimate.lean:474`);
* `(concreteVariantData D).rhsData.rhs` is the lana right-hand side `-|log Θ|`.

The two glue inputs are concrete targets:
`HIdentTarget C3 D : -|thetaPilotHullLogVolumeReal C3| = (concreteVariantData D).rhsData.rhs`,
`HATarget D ell d f q eta C : lanaRhsBoundValue (concreteVariantData D) D.invariants
   = shellUpperBoundA ell d f q eta C`.

Expected now: import FAIL (no lana olean yet); no other local error is claimed.  No
RETRACTED file referenced; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundLanaInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundLanaActual
open scoped BigOperators ENNReal

universe u

/-- Concrete lana variant data `X` of `D`. -/
noncomputable abbrev lanaX (D : Iut.InitialThetaData.{u}) :
    Iut.Corollary312VariantData.{u} :=
  Iut.concreteVariantData D

/-- Concrete lana invariants `inv` of `D`. -/
noncomputable abbrev lanaInv (D : Iut.InitialThetaData.{u}) :
    Iut.Theorem110Invariants (lanaX D) :=
  D.invariants

/-- Concrete lana local estimate `est` from `TA : TowerArithmetic D`. -/
noncomputable abbrev lanaEst (D : Iut.InitialThetaData.{u})
    (TA : Iut.TowerArithmetic D) : (lanaInv D).LocalEstimate :=
  Iut.TowerArithmetic.localEstimate TA

/-- **Concrete lana `rhs_le`** for `D` and `TA`: the actual right-hand side is at
most the explicit lana bound value. -/
theorem concrete_lana_rhs_le (D : Iut.InitialThetaData.{u})
    (TA : Iut.TowerArithmetic D) :
    (lanaX D).rhsData.rhs ≤ lanaRhsBoundValue (lanaX D) (lanaInv D) :=
  lana_rhs_le (lanaX D) (lanaInv D) (lanaEst D TA)

/-- **Concrete `hident` target**: our real Theta-pilot hull log-volume reading equals
lana's right-hand side for `X = concreteVariantData D`. -/
def HIdentTarget {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : Iut.InitialThetaData.{u}) : Prop :=
  -|thetaPilotHullLogVolumeReal C3| = (lanaX D).rhsData.rhs

/-- **Concrete `hA` target**: lana's bound value equals the paper skeleton
`A(ell,d,f,q,η)`. -/
def HATarget (D : Iut.InitialThetaData.{u}) (ell : PrimeGeFive)
    (d f : Nat) (q eta C : Real) : Prop :=
  lanaRhsBoundValue (lanaX D) (lanaInv D) = shellUpperBoundA ell d f q eta C

/-- **Concrete thin consumer**: the two glue targets (as hypotheses) plus lana
`rhs_le` for the concrete data give `GlobalShellAssembly`. -/
theorem globalShellAssembly_of_lana_concrete
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : Iut.InitialThetaData.{u}) (TA : Iut.TowerArithmetic D)
    (ell : PrimeGeFive) (d f : Nat) (q eta C : Real)
    (hident : HIdentTarget (u := u) C3 D)
    (hA : HATarget (u := u) D ell d f q eta C) :
    GlobalShellAssembly C3 ell d f q eta C := by
  have hle : -|thetaPilotHullLogVolumeReal C3| ≤ shellUpperBoundA ell d f q eta C := by
    rw [hident, ← hA]
    exact concrete_lana_rhs_le D TA
  unfold GlobalShellAssembly ShellVolumeUpperBoundShape
  exact hle

def lanaInstanceRows : List (String × String × String) :=
  [ ("concrete X", "Iut.concreteVariantData D", "lana def (ThetaRegion:359)"),
    ("concrete inv", "Iut.InitialThetaData.invariants D", "lana def (Invariants:262)"),
    ("concrete TA", "Iut.TowerArithmetic D", "lana structure (Invariants:287)"),
    ("concrete est", "Iut.TowerArithmetic.localEstimate TA", "lana def (LocalEstimate:474)"),
    ("concrete rhs_le", "concrete_lana_rhs_le", "uses lana rhs_le"),
    ("glue targets", "HIdentTarget / HATarget", "DEF (specific, no named structure)"),
    ("(U) consumer", "globalShellAssembly_of_lana_concrete", "CONDITIONAL on hident/hA"),
    ("scope", "ABC gate NOT passed; no RETRACTED reference", "INTEGRITY") ]

theorem lanaInstanceRows_length : lanaInstanceRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundLanaInstanceActual

end