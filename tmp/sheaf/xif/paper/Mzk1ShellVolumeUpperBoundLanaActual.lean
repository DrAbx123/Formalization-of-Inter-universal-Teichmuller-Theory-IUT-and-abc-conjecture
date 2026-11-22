/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.lana.Iut.Implication.LogVolumeBound
import tmp.external.ported.lana.Iut.Concrete.LocalEstimate
import tmp.sheaf.xif.paper.Mzk1ShellVolumeUpperBoundActual

/-! # A726 hull: (U) consumer wired to lana's compiled `rhs_le` / `localEstimate`

This file is the **thin consumer** that replaces the two named inputs of
`Mzk1ShellVolumeUpperBoundActual` by references to lana's proved theorems:

* `Iut.Theorem110Invariants.LocalEstimate.rhs_le` — IUT IV Steps (iv)–(vii) global
  assembly (source: `tmp/external/ported/lana/Iut/Implication/LogVolumeBound.lean`);
* `Iut.TowerArithmetic.localEstimate` — concrete local estimates
  (`tmp/external/ported/lana/Iut/Concrete/LocalEstimate.lean`).

The bridge keeps the identification `-|logΘ| = X.rhsData.rhs` and the arithmetic
identification `lanaRhsBoundValue X inv = A(l,d,f,q,η)` as explicit hypotheses; once
the two lana modules compile, these are the only glue inputs, and `GlobalShellAssembly`
is a theorem (no named field).  The import currently FAILs only because the lana
modules have no olean yet (expected); the theorem names/types below are taken from
the actual sources.

No RETRACTED file referenced; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundLanaActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual
open scoped BigOperators ENNReal

universe u

/-- The exact right-hand side value of lana's `rhs_le`. -/
noncomputable def lanaRhsBoundValue (X : Iut.Corollary312VariantData.{u})
    (inv : Iut.Theorem110Invariants X) : Real :=
  (∑ i : Fin X.rhsData.container.proc.length,
    (∑ p ∈ inv.dst, inv.capsuleBound (X.rhsData.container.proc.capsule i).card p +
      (X.rhsData.container.proc.capsule i).card * Real.log (Real.sqrt 2 * Real.pi))) /
    X.rhsData.container.proc.length

/-- **lana `rhs_le` (IUT IV Steps (iv)–(vii))**, restated with the explicit bound
value.  Source name/type:
`Iut.Theorem110Invariants.LocalEstimate.rhs_le`
`(inv : Theorem110Invariants X) (est : inv.LocalEstimate)`.
Once the lana port compiles this is a proved theorem (0 sorry). -/
theorem lana_rhs_le (X : Iut.Corollary312VariantData.{u})
    (inv : Iut.Theorem110Invariants X) (est : inv.LocalEstimate) :
    X.rhsData.rhs ≤ lanaRhsBoundValue X inv :=
  Iut.Theorem110Invariants.LocalEstimate.rhs_le inv est

/-- **lana concrete `localEstimate`** (local-field content):
`Iut.TowerArithmetic.localEstimate (TA : TowerArithmetic D) : (D.invariants).LocalEstimate`. -/
noncomputable def lanaLocalEstimate {D : Iut.InitialThetaData.{u}}
    (TA : Iut.TowerArithmetic D) : (D.invariants).LocalEstimate :=
  Iut.TowerArithmetic.localEstimate TA

/-- **Thin consumer**: given (i) the identification of `-|logΘ|` with lana's
`X.rhsData.rhs`, and (ii) the arithmetic identification of lana's bound value with
`A(l,d,f,q,η)`, lana's `rhs_le` proves the `(U)` shape as `GlobalShellAssembly`. -/
theorem globalShellAssembly_of_lana
    (X : Iut.Corollary312VariantData.{u})
    (inv : Iut.Theorem110Invariants X) (est : inv.LocalEstimate)
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (ell : PrimeGeFive) (d f : Nat) (q eta C : Real)
    (hident : -|thetaPilotHullLogVolumeReal C3| = X.rhsData.rhs)
    (hA : lanaRhsBoundValue X inv = shellUpperBoundA ell d f q eta C) :
    GlobalShellAssembly C3 ell d f q eta C := by
  have hle : -|thetaPilotHullLogVolumeReal C3| ≤ shellUpperBoundA ell d f q eta C := by
    rw [hident, ← hA]
    exact lana_rhs_le X inv est
  unfold GlobalShellAssembly ShellVolumeUpperBoundShape
  exact hle

def lanaConsumerRows : List (String × String × String) :=
  [ ("lana rhs_le", "Iut.Theorem110Invariants.LocalEstimate.rhs_le", "PROVED in lana port (pending olean)"),
    ("lana localEstimate", "Iut.TowerArithmetic.localEstimate", "PROVED in lana port (pending olean)"),
    ("(U) consumer", "globalShellAssembly_of_lana", "CONDITIONAL on hident/hA; no named"),
    ("scope", "replaces GlobalShellAssembly named; ABC gate NOT passed", "INTEGRITY") ]

theorem lanaConsumerRows_length : lanaConsumerRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundLanaActual.globalShellAssembly_of_lana

end LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundLanaActual

end