import tmp.sheaf.xif.paper.Mzk1ThetaDataLegalityActual
import tmp.sheaf.xif.paper.Mzk1LocalVolumeAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import Mathlib.Tactic

/-!
# A861 G5: D_exact lower-bound target, L1–L7 naming, exception table (shehdd)

§12.1 L1–L7 assembly, aligned with hull's `Mzk1LocalVolumeAssemblyActual` and the
abc L6 form (`L6ReducedInequality`):

* L1 shell volume: `logMuPaper` (hull);
* L2 tame shell exponent: `tameShellExponent` (hull);
* L3 hull packet: `hullPacketShape` (hull);
* L4 procession average: `avgJPlusOneShape = (l+5)/4` (hull);
* L5 capsule average: `avgJSquareShape = l(l+1)/12 = sL l` (hull);
* L6 assembly: `assembledVolume l D = ((l+5)/4)·D` (hull); the abc-side reduction is
  `L6ReducedInequality C l D_exact := e·log p ≤ T(l)·D_exact`;
* L7 target: `DExactLowerTarget C l D_exact := (1 - 1/l)·log p ≤ D_exact`.

Proved: the naming/arithmetic lemmas, `l6Reduced_of_dExactLower` (L6 reduction given
the target), and the exception-prime table {11,17,19,37} with primality proofs.
The actual `e_p` values at the exceptions are EXTERNAL data, recorded as such (no
invented numbers).  The single remaining content is `DExactLowerTarget` (L7).

No RETRACTED statement.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual

open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1LocalVolumeAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open scoped BigOperators

/-- L1: shell-volume local term (hull's `logMuPaper`). -/
def L1ShellVolume (p e r n : ℝ) : ℝ := logMuPaper p e r n

/-- L2: tame shell exponent (hull's `tameShellExponent`). -/
def L2TameExponent (e : ℝ) : ℝ := tameShellExponent e

/-- L3: hull packet shape (hull's `hullPacketShape`). -/
def L3HullPacket {ι : Type*} [Fintype ι] (w rho : ι → ℝ) (logp : ℝ) : ℝ :=
  hullPacketShape w rho logp

/-- L4: procession average `(l+5)/4` (hull's `avgJPlusOneShape`). -/
def L4ProcessionAverage (l : ℝ) : ℝ := avgJPlusOneShape l

/-- L5: capsule average `l(l+1)/12` (hull's `avgJSquareShape` = `sL l`). -/
def L5CapsuleAverage (l : ℝ) : ℝ := avgJSquareShape l

theorem L5CapsuleAverage_eq_sL (l : ℝ) :
    L5CapsuleAverage l = sL l := by
  unfold L5CapsuleAverage avgJSquareShape sL
  ring

/-- L6: assembled volume `((l+5)/4)·D` (hull's `assembledVolume`). -/
def L6Assembly (l D : ℝ) : ℝ := assembledVolume l D

/-- L7: the §12.1 target `D_exact ≥ (1 - 1/l)·log p`. -/
def DExactLowerTarget (C : PrimeConductorCurve) (l D_exact : ℝ) : Prop :=
  (1 - 1 / l) * Real.log (C.p : ℝ) ≤ D_exact

/-- L6 reduction: the L7 target plus Mestre–Oesterlé and Θ-data legality gives the
abc L6 inequality `e·log p ≤ T(l)·D_exact`. -/
theorem l6Reduced_of_dExactLower
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℕ) (L : ThetaDataLegality C l) (D_exact : ℝ)
    (hD : DExactLowerTarget C (l : ℝ) D_exact)
    (hlogp : 0 ≤ Real.log (C.p : ℝ)) :
    L6ReducedInequality C (l : ℝ) D_exact := by
  have hl11 : (11 : ℝ) ≤ (l : ℝ) := by exact_mod_cast L.l_ge_11
  exact paperGap_of_primeConductor_arith hMO C (l : ℝ) hl11 hlogp D_exact hD

/-- Consumer: the L7 target yields `SSIneqExplicit` (via the A845 bridge). -/
theorem ssIneqExplicit_of_dExactLower
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℕ) (L : ThetaDataLegality C l) (D_exact : ℝ)
    (hD : DExactLowerTarget C (l : ℝ) D_exact)
    (hlogp : 0 ≤ Real.log (C.p : ℝ)) :
    SSIneqExplicit (sL (l : ℝ))
      ((C.e : ℝ) * Real.log (C.p : ℝ)) (l : ℝ)
      ((((l : ℝ) + 5) / 4) * D_exact) := by
  have hl11 : (11 : ℝ) ≤ (l : ℝ) := by exact_mod_cast L.l_ge_11
  exact paperGap_of_primeConductor hMO C (l : ℝ) hl11 hlogp D_exact hD

/-- Exception primes of the Mestre–Oesterlé statement: {11,17,19,37}. -/
def classicExceptionPrimes : List ℕ := [11, 17, 19, 37]

theorem classicExceptionPrimes_prime :
    ∀ p ∈ classicExceptionPrimes, Nat.Prime p := by
  decide

theorem classicExceptionPrimes_length : classicExceptionPrimes.length = 4 := rfl

/-- Exception-table row: the `e_p` value at the exception is EXTERNAL published data,
not asserted here. -/
structure ExceptionRecord where
  p : ℕ
  e_p : Option ℕ
  note : String
  deriving Repr, DecidableEq

def exceptionRecords : List ExceptionRecord :=
  [ ⟨ 11, none, "Mestre-Oesterle exception (p>37 bound excluded); e_p <= 5 is the published bound; exact value EXTERNAL" ⟩
  , ⟨ 17, none, "Mestre-Oesterle exception; e_p <= 5 EXTERNAL" ⟩
  , ⟨ 19, none, "Mestre-Oesterle exception; e_p <= 5 EXTERNAL" ⟩
  , ⟨ 37, none, "Mestre-Oesterle exception; e_p <= 5 EXTERNAL" ⟩
  ]

theorem exceptionRecords_primes :
    exceptionRecords.map (fun r => r.p) = classicExceptionPrimes := rfl

theorem exceptionRecords_all_external :
    exceptionRecords.all (fun r => r.e_p = none) = true := by
  decide

structure LRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def lRows : List LRow :=
  [ ⟨"L1 shell volume", "logMuPaper (hull)", "GREEN / arithmetic"⟩
  , ⟨"L2 tame exponent", "tameShellExponent (hull)", "GREEN / arithmetic"⟩
  , ⟨"L3 hull packet", "hullPacketShape (hull)", "GREEN / arithmetic"⟩
  , ⟨"L4 procession average", "avgJPlusOneShape = (l+5)/4 (hull)", "GREEN"⟩
  , ⟨"L5 capsule average", "avgJSquareShape = l(l+1)/12 = sL l (hull+P7)", "PROVED (L5CapsuleAverage_eq_sL)"⟩
  , ⟨"L6 assembly", "assembledVolume l D = ((l+5)/4)D; L6ReducedInequality", "GREEN; l6Reduced_of_dExactLower"⟩
  , ⟨"L7 D_exact lower target", "DExactLowerTarget = (1-1/l)log p <= D_exact", "PENDING (geometric L1-L7 inputs)"⟩
  , ⟨"exception table", "{11,17,19,37}; e_p values EXTERNAL, no invented numbers", "RECORDED_AS_EXTERNAL"⟩
  , ⟨"scope", "no fake D_exact bound; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem lRows_length : lRows.length = 9 := rfl

theorem lRows_has_pending :
    lRows.any (fun r => r.status = "PENDING (geometric L1-L7 inputs)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual.L5CapsuleAverage_eq_sL
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual.l6Reduced_of_dExactLower
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual.ssIneqExplicit_of_dExactLower
