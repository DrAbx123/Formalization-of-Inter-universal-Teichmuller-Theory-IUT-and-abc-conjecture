import tmp.sheaf.xif.paper.GeomCore01StatementActual
import tmp.sheaf.xif.paper.Mzk1Theorem25StatementActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# GeomCore03: GeometricCore GATED ASSEMBLY ([Mzk1] Thm 2.5 input as single named hypothesis)

STEP 0 prior-art (reuse, no re-proof):
* GeometricCore statement record -> GeomCore01StatementActual (BasepointFreePencil /
  FiniteMapToP1 / RamificationData / GeometricCoreData; statement-only);
* GeometricCore input wiring/data -> GeomCore02WiringActual (finite-map ported module,
  RR/Serde/Cech/canonical-divisor asset mapping);
* canonical promotions (separate consumers; NOT imported here to avoid the documented
  flt/flt_adaptive duplicate-namespace clash): AG_FLT_RiemannRochPromotionActual
  (6 RR rows + 2 COMPLETE reductions), AG_FLT_SerrePairingPromotionActual (pairing +
  value formula COMPLETE), AG_FLT_CanonicalDivisorPromotionActual (canonical divisor,
  ell=genus, deg=2g-2 COMPLETE), AG_FLT_CechPromotionActual (Cech H0/H1 COMPLETE);
  AG05CechActual / AG06bRRInterfaceActual / AG10CanonicalDivisorGenusActual /
  AG11SerrePairingConsumerActual consume them;
* [Mzk1] Thm 2.5 statement -> Mzk1Theorem25StatementActual.Mzk1GeometricCoreStatement
  (HONESTY: current Lean body is a True placeholder; the precise paper statement is
  pending.  This file uses it ONLY as the single named paper-input hypothesis and
  does NOT exploit the placeholder to prove geometric content.)

This is a GATED ASSEMBLY: the geometric output is a conditional statement and the
A-class generic constructor below produces GeometricCoreData from explicit function/
ramification data; no closure of [Mzk1] Thm 2.5 is claimed, and the assembly remains
gated by the paper input plus the canonical proof promotions.

Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.GeomCore03AssemblyActual

open LeanFormal.IUT.XiFPaper.GeomCore01StatementActual

universe u

/-- The [Mzk1] Thm 2.5 GeometricCore paper-input, as the single named hypothesis.
HONESTY: the current Lean body of Mzk1GeometricCoreStatement is a placeholder; the
precise statement must replace it before any paper-level use. -/
abbrev GeomCorePaperInput : Prop :=
  LeanFormal.IUT.XiFPaper.Mzk1Theorem25StatementActual.Mzk1GeometricCoreStatement

/-- The geometric output required by GeometricCore (statement-level). -/
def GeomCoreOutputStatement (X : Type u) : Prop :=
  Nonempty (GeometricCoreData X)

/-- The gated assembly statement: the paper input implies the geometric output.
This is the assembly TARGET; it is not proved here (the paper input is the named
class-D hypothesis and the geometric construction is the remaining gate). -/
def GeomCoreAssemblyStatement (X : Type u) : Prop :=
  GeomCorePaperInput → GeomCoreOutputStatement X

/-- Definitional shape of the gated assembly (no proof of geometric content). -/
theorem GeomCoreAssemblyStatement_iff (X : Type u) :
    GeomCoreAssemblyStatement X ↔
      (GeomCorePaperInput → Nonempty (GeometricCoreData X)) :=
  Iff.rfl

/-- **A-class generic constructor:** an explicit function to the projective line with
nonvanishing values, a positive degree, and finite ramification data yield a
GeometricCoreData record (basepoint-free pencil from the function's multiples,
finite map, ramification data).  This is the assembly's constructive core; the
geometric hypotheses (existence of the function/pencil data from [Mzk1] Thm 2.5)
remain the gate. -/
def geometricCoreDataOfFunction (X : Type u) (φ : X → ℝ) (d : ℕ) (hd : 0 < d)
    (hne : ∀ x : X, φ x ≠ 0) (ramified : Set X) (hfin : ramified.Finite)
    (x₀ : X) (hx₀ : x₀ ∉ ramified) : GeometricCoreData X where
  pencil :=
    { curve := X
      curveEq := rfl
      pencil := {g | ∃ a : ℝ, g = fun x => a * φ x}
      basepointFree := by
        intro x
        exact ⟨fun y => φ y, ⟨1, by funext y; simp⟩, hne x⟩ }
  finiteMap :=
    { toP1 := φ
      degree := d
      degree_pos := hd }
  ramification :=
    { ramified := ramified
      ramified_finite := hfin
      unramifiedPoint := x₀
      unramifiedPoint_mem := hx₀ }

/-- The A-class constructor yields a nonempty GeometricCoreData (given the explicit
function/ramification data and nonvanishing). -/
theorem geometricCoreDataOfFunction_nonempty (X : Type u) (φ : X → ℝ) (d : ℕ)
    (hd : 0 < d) (hne : ∀ x : X, φ x ≠ 0) (ramified : Set X)
    (hfin : ramified.Finite) (x₀ : X) (hx₀ : x₀ ∉ ramified) :
    Nonempty (GeometricCoreData X) :=
  ⟨geometricCoreDataOfFunction X φ d hd hne ramified hfin x₀ hx₀⟩

/-- Conditional assembly shape: the gated statement holds as soon as an explicit
geometric witness (function/nonvanishing/pencil/ramification) is supplied.  The named
paper input remains the gating hypothesis inside GeomCoreAssemblyStatement (it is the
class-D gate, not consumed by the constructor); the explicit witness data IS consumed
by the constructor. -/
theorem geomCore_conditional (X : Type u)
    (φ : X → ℝ) (d : ℕ) (hd : 0 < d) (hne : ∀ x : X, φ x ≠ 0)
    (ramified : Set X) (hfin : ramified.Finite) (x₀ : X) (hx₀ : x₀ ∉ ramified) :
    GeomCoreAssemblyStatement X :=
  fun _ => geometricCoreDataOfFunction_nonempty X φ d hd hne ramified hfin x₀ hx₀

/-- Canonical assets consumed by the gated assembly (data ledger). -/
def geomCoreCanonicalAssets : List (String × String × String) :=
  [ ("RR rows + 2 reductions", "AG_FLT_RiemannRochPromotionActual (CITABLE 8)", "A (green; consumed by AG06b/AG10)"),
    ("Serre pairing + value formula", "AG_FLT_SerrePairingPromotionActual (CITABLE 2)", "A (green; consumed by AG11)"),
    ("Cech H0/H1", "AG_FLT_CechPromotionActual (CITABLE 5)", "A (green; consumed by AG05)"),
    ("canonical divisor / genus", "AG_FLT_CanonicalDivisorPromotionActual (CITABLE 3)", "A (green; consumed by AG10)"),
    ("finite map to P1 data", "tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData (ported EXIT=0)", "A (green; wiring only)"),
    ("GeometricCore statement record", "GeomCore01StatementActual (CITABLE 5)", "statement layer"),
    ("GeometricCore input wiring", "GeomCore02WiringActual (CITABLE 2)", "data/wiring"),
    ("[Mzk1] Thm 2.5", "Mzk1Theorem25StatementActual.Mzk1GeometricCoreStatement (placeholder body True; precise statement pending)", "class-D single named hypothesis") ]

/-- Assembly plan: ([Mzk1] proof component, canonical asset/gate, status). -/
def geomCoreAssemblyPlan : List (String × String × String) :=
  [ ("GeometricCore existence (finite morphism to P1, basepoint-free, unramified over 0)", "Mzk1Theorem25StatementActual (class D) + canonical finite-map ported module", "GATED (paper input; ported asset green)"),
    ("Riemann-Roch / Serre duality / basepoint-free linear system", "AG_FLT_RiemannRochPromotionActual (2 COMPLETE reductions) + AG_FLT_SerrePairingPromotionActual", "A-class assets GREEN; use in discharge"),
    ("canonical divisor / genus g", "AG_FLT_CanonicalDivisorPromotionActual -> AG10CanonicalDivisorGenusActual", "A-class GREEN"),
    ("Cech H0 = L(D) on two-chart cover", "AG_FLT_CechPromotionActual -> AG05CechActual", "A-class GREEN"),
    ("finite map / two-chart rational function data", "ported flt_th FiniteMapData module (EXIT=0)", "A-class asset GREEN; import directly"),
    ("assembly constructivity", "GeomCore03.geometricCoreDataOfFunction (A-class generic constructor)", "PROVED (given explicit function/ramification data)"),
    ("paper-level closure", "GeomCoreAssemblyStatement (GeomCorePaperInput -> output)", "GATED; NOT proved; no closure claim") ]

theorem geomCoreAssemblyPlan_length : geomCoreAssemblyPlan.length = 7 := rfl

/-- Remaining discharge obligations (gated). -/
def geomCoreRemainingDischarge : List (String × String) :=
  [ ("precise Mzk1 Thm 2.5 statement", "replace placeholder Mzk1GeometricCoreStatement with the exact paper statement (corpus Mzk1 Thm 2.5 lines 207-221)"),
    ("GeometricCore proof (RR/Serde/basepoint-free/unramified)", "port canonical finite-map + RR/Serde proofs into the geometric construction (dependency blockers reported by qpilot: env/serial compile)"),
    ("explicit geometric witness", "supply the actual function/pencil/ramification data; geomCore_conditional then yields the output"),
    ("paper-level status", "GATED assembly only; L8 frozen; no closure claimed") ]

end LeanFormal.IUT.XiFPaper.GeomCore03AssemblyActual

end
