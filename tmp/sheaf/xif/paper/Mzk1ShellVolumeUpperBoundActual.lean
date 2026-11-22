/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # A704 hull: N2 preparation — the concrete shell volume upper bound shape (U)

Source: IUT IV, Propositions 1.2–1.4 (log-shell volume / local lattice computation).

The paper's upper bound has the shape

  (U)  `-|log Θ| ≤ A(l, d, f, q, η)`

where `l` is the prime, `d`, `f`, `q`, `η` are the paper quantities.  Following the
source skeleton of Prop. 1.2–1.4 we register

  `A(l,d,f,q,η) = C + log l + d·log q + f·log η`

with the numerical constant `C` kept as an **explicit parameter** (we do NOT claim
its value is proved).  The unproved local lattice computation is recorded as the
named predicate `LocalLatticeComputationAtPlace` (a concrete inequality, NOT an
axiom and NOT a `True` field); the global assembly over the triple-dependent N1 data
is recorded as `GlobalShellAssembly`.

Reused green machine (same file): `S3137QThetaPilotLogVolumeReadingsActual`

* `thetaPilotHull = actualC3LogShellTensorRegion C3`;
* `thetaPilotHullLogVolume`, `thetaPilotHullLogVolume_eq_regionLogVolume`;
* `thetaPilotHullLogVolumeReal`, `thetaPilotHullLogVolumeReal_eq_regionLogVolume`.

No RETRACTED `hfull`/`N`-scaling file is referenced.  ABC gate NOT passed;
no canonical object changed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open MeasureTheory
open scoped BigOperators ENNReal

/-- Paper expression skeleton `A(l,d,f,q,η) = C + log l + d·log q + f·log η`;
the constant `C` is an explicit parameter (its numerical value is not claimed). -/
noncomputable def shellUpperBoundA
    (l : PrimeGeFive) (d f : Nat) (q eta C : Real) : Real :=
  C + Real.log (l.value : Real) + (d : Real) * Real.log q + (f : Real) * Real.log eta

/-- **(U) shape**: `-|log Θ| ≤ A(l,d,f,q,η)`. -/
def ShellVolumeUpperBoundShape
    (l : PrimeGeFive) (d f : Nat) (q eta C logTheta : Real) : Prop :=
  -|logTheta| ≤ shellUpperBoundA l d f q eta C

/-- **Named local lattice computation** (IUT IV Prop. 1.2–1.3), at one place:
the local log-shell volume `logTheta` is bounded in absolute value by the paper
skeleton.  This is a concrete Prop (not an axiom, not `True`). -/
def LocalLatticeComputationAtPlace
    (l : PrimeGeFive) (d f : Nat) (q eta C logTheta : Real) : Prop :=
  |logTheta| ≤ shellUpperBoundA l d f q eta C

/-- **(U) follows from the named local lattice computation** when the skeleton is
nonnegative. -/
theorem shellVolumeUpperBoundShape_of_localLattice
    (l : PrimeGeFive) (d f : Nat) (q eta C logTheta : Real)
    (hA : 0 ≤ shellUpperBoundA l d f q eta C)
    (h : LocalLatticeComputationAtPlace l d f q eta C logTheta) :
    ShellVolumeUpperBoundShape l d f q eta C logTheta := by
  unfold LocalLatticeComputationAtPlace ShellVolumeUpperBoundShape at *
  have hstep : -|logTheta| ≤ |logTheta| := by
    have hnn := abs_nonneg logTheta
    linarith
  exact le_trans hstep h

/-! ## Reused actual Theta-pilot hull machine -/

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance shellBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance shellBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual Theta-pilot hull log-volume reading is the region log-volume
(green `S3137` identity): log form of the hull volume. -/
theorem thetaPilotHullLogVolumeReal_eq_regionLogVolume' :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_regionLogVolume C3

/-- The ENNReal hull log-volume is the region log-volume (green `S3137` identity). -/
theorem thetaPilotHullLogVolume_eq_regionLogVolume' :
    thetaPilotHullLogVolume C3 =
      haarLogVolume (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3) :=
  thetaPilotHullLogVolume_eq_regionLogVolume C3

/-- **Named global shell assembly** (IUT IV Prop. 1.4): on the triple-dependent N1
Theta data, the actual hull log-volume reading satisfies the (U) shape with the
paper skeleton.  Concrete Prop, not an axiom. -/
def GlobalShellAssembly
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (l : PrimeGeFive) (d f : Nat) (q eta C : Real) : Prop :=
  ShellVolumeUpperBoundShape l d f q eta C (thetaPilotHullLogVolumeReal C3)

/-- **Parameterized `rhs_le`-style upper bound** on the real hull log-volume.  This is
the exact shape produced by lana's `rhs_le`/`globalVol_thetaHull_le` once their
`Iut.Implication.LogVolumeBound` is compiled; it is kept as a plain `Prop` so the
replacement interface does not depend on any uncompiled file. -/
def RhsLeUpperBound
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real -> Prop :=
  fun A => -|thetaPilotHullLogVolumeReal C3| <= A

/-- **Replacement interface**: a `rhs_le`-style upper bound yields the global shell
assembly (the `(U)` shape).  Once lana `rhs_le` is available, its conclusion is fed
here; the named `GlobalShellAssembly` can then be discharged by this theorem. -/
theorem globalAssembly_of_rhs_le
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (l : PrimeGeFive) (d f : Nat) (q eta C A : Real)
    (hA : A = shellUpperBoundA l d f q eta C)
    (hrhs : RhsLeUpperBound C3 A) :
    GlobalShellAssembly C3 l d f q eta C := by
  unfold GlobalShellAssembly ShellVolumeUpperBoundShape RhsLeUpperBound at *
  simpa [hA] using hrhs

/-- Alias of `shellVolumeUpperBoundShape_of_localLattice` with the stable interface
name used by the N2 plan: local lattice computation implies `(U)`. -/
theorem localLattice_implies_U
    (l : PrimeGeFive) (d f : Nat) (q eta C logTheta : Real)
    (hA : 0 <= shellUpperBoundA l d f q eta C)
    (h : LocalLatticeComputationAtPlace l d f q eta C logTheta) :
    ShellVolumeUpperBoundShape l d f q eta C logTheta :=
  shellVolumeUpperBoundShape_of_localLattice l d f q eta C logTheta hA h

/-! ## Monotonicity of the (U) shape in the paper quantities -/

theorem shellUpperBoundA_mono_q
    (l : PrimeGeFive) (d f : Nat) (q q' eta C : Real)
    (hq0 : 0 < q) (hq : q ≤ q') :
    shellUpperBoundA l d f q eta C ≤ shellUpperBoundA l d f q' eta C := by
  unfold shellUpperBoundA
  have hlog : Real.log q ≤ Real.log q' := Real.log_le_log hq0 hq
  have hd : (0 : Real) ≤ (d : Real) := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left hlog hd]

theorem shellUpperBoundA_mono_eta
    (l : PrimeGeFive) (d f : Nat) (q eta eta' C : Real)
    (heta0 : 0 < eta) (heta : eta ≤ eta') :
    shellUpperBoundA l d f q eta C ≤ shellUpperBoundA l d f q eta' C := by
  unfold shellUpperBoundA
  have hlog : Real.log eta ≤ Real.log eta' := Real.log_le_log heta0 heta
  have hf : (0 : Real) ≤ (f : Real) := Nat.cast_nonneg f
  nlinarith [mul_le_mul_of_nonneg_left hlog hf]

/-- Monotonicity of the (U) shape in the right-hand side. -/
theorem shellVolumeUpperBoundShape_mono_A
    (l : PrimeGeFive) (d f : Nat) (q eta C C' logTheta : Real)
    (hC : shellUpperBoundA l d f q eta C ≤ shellUpperBoundA l d f q eta C')
    (h : ShellVolumeUpperBoundShape l d f q eta C logTheta) :
    ShellVolumeUpperBoundShape l d f q eta C' logTheta := by
  unfold ShellVolumeUpperBoundShape at *
  linarith

/-- (U) shape is monotone in `q` for positive `q`. -/
theorem shellVolumeUpperBoundShape_mono_q
    (l : PrimeGeFive) (d f : Nat) (q q' eta C logTheta : Real)
    (hq0 : 0 < q) (hq : q ≤ q')
    (h : ShellVolumeUpperBoundShape l d f q eta C logTheta) :
    ShellVolumeUpperBoundShape l d f q' eta C logTheta := by
  unfold ShellVolumeUpperBoundShape at *
  linarith [shellUpperBoundA_mono_q l d f q q' eta C hq0 hq]

def shellVolumeRows : List (String × String × String) :=
  [ ("A skeleton", "A(l,d,f,q,η) = C + log l + d·log q + f·log η", "DEF (C explicit parameter)"),
    ("(U) shape", "ShellVolumeUpperBoundShape", "DEF (-|logΘ| ≤ A)"),
    ("local lattice named input", "LocalLatticeComputationAtPlace", "NAMED (not axiom, not True)"),
    ("(U) from local lattice", "shellVolumeUpperBoundShape_of_localLattice", "PROVED (conditional on named input)"),
    ("actual hull log form", "thetaPilotHullLogVolumeReal_eq_regionLogVolume'", "PROVED (green S3137)"),
    ("global shell assembly named input", "GlobalShellAssembly", "NAMED (IUT IV Prop 1.4)"),
    ("(U) monotone in q", "shellVolumeUpperBoundShape_mono_q", "PROVED"),
    ("(U) monotone in η", "shellUpperBoundA_mono_eta", "PROVED"),
    ("replacement interface (lana rhs_le)", "globalAssembly_of_rhs_le", "PARAMETRIC (compiles without lana)"),
    ("stable interface name", "localLattice_implies_U", "PROVED (alias)"),
    ("scope", "N2 preparation; local lattice computation NOT proved; ABC gate NOT passed", "INTEGRITY") ]

theorem shellVolumeRows_length : shellVolumeRows.length = 11 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual.shellVolumeUpperBoundShape_of_localLattice
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual.thetaPilotHullLogVolumeReal_eq_regionLogVolume'
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual.shellVolumeUpperBoundShape_mono_q
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual.globalAssembly_of_rhs_le
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual.localLattice_implies_U

end LeanFormal.IUT.XiFPaper.Mzk1ShellVolumeUpperBoundActual

end