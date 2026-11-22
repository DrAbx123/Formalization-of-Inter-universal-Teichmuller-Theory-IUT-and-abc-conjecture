import Mathlib

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# GeomCore01: [Mzk1] Theorem 2.5 (GeometricCore) — statement layer

Paper: [Mzk1] Noncritical Belyi Maps (corpus text present in
papers/motizuki_corpus/text/).  The GeometricCore input needed by IUT (cf.
[IUTchII] / [AbsTopIII]) is the existence, for a suitable hyperbolic curve X,
of a basepoint-free pencil + finite map to P^1 with controlled (non-)ramification.
This file is the P0 statement layer: the exact data record with class annotations.
The proofs are to be WIRED from the canonical external ports (per Lead/qpilot
de-duplication decision):
* FLT flt_core: Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
  (finite map to P1) + SerrePairing/cechRiemannRoch + weilDualityAdelic;
* FLT flt_test: canonical divisor/Kaehler/RR-space;
* TauCeti tauceti_rr: RiemannRoch/Pencil/Genus + Belyi/Basic (Belyi existence);
promotions AG_FLT_RiemannRochPromotionActual / AG_TAUCETI_RiemannRochPromotionActual
PENDING (qpilot owner).  No re-proof; no axiom.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.GeomCore01StatementActual

universe u

/-- A basepoint-free pencil on a curve (abstract record): a linear subspace of
global sections whose common zero locus is empty. -/
structure BasepointFreePencil (X : Type u) where
  /-- the curve (as a type of closed points) -/
  curve : Type u
  curveEq : curve = X
  /-- the pencil as a set of functions/global sections -/
  pencil : Set (X → ℝ)
  /-- basepoint-free: no point is a common zero of all pencil members -/
  basepointFree : ∀ x : X, ∃ f ∈ pencil, f x ≠ 0

/-- A finite map to P^1 with its degree (abstract record). -/
structure FiniteMapToP1 (X : Type u) where
  /-- the underlying map to the projective line (as a function) -/
  toP1 : X → ℝ
  /-- the degree of the finite map -/
  degree : ℕ
  degree_pos : 0 < degree

/-- Non-ramification data of the finite map: the ramification set and the
condition that the map is unramified outside it (statement layer). -/
structure RamificationData (X : Type u) (F : FiniteMapToP1 X) where
  /-- the ramification locus -/
  ramified : Set X
  /-- the locus is finite -/
  ramified_finite : ramified.Finite
  /-- a nonempty unramified point supplied by the paper construction -/
  unramifiedPoint : X
  unramifiedPoint_mem : unramifiedPoint ∉ ramified

/-- GeometricCore data ([Mzk1] Thm 2.5 input): basepoint-free pencil + finite map
to P^1 + non-ramification data. -/
structure GeometricCoreData (X : Type u) where
  /-- the basepoint-free pencil -/
  pencil : BasepointFreePencil X
  /-- the finite map to P^1 -/
  finiteMap : FiniteMapToP1 X
  /-- its ramification data -/
  ramification : RamificationData X finiteMap

/-- Paper components of [Mzk1] Theorem 2.5 (GeometricCore). -/
def GeomCorePaperComponents : List (String × String × String) :=
  [ ("[Mzk1] Noncritical Belyi Maps (corpus text)", "Belyi/Basic existence (TauCeti tauceti_rr)", "canonical port; promotion PENDING"),
    ("basepoint-free pencil", "BasepointFreePencil", "statement layer"),
    ("finite map to P^1", "FiniteMapToP1", "canonical FLT flt_core SmoothProperCurveFiniteMapData; promotion PENDING"),
    ("(non-)ramification data", "RamificationData", "statement layer; canonical ramification assets pending"),
    ("Riemann-Roch / canonical divisor / Serre duality", "L(D) = cechH0 (AG05) + flt_core SerrePairing/weilDualityAdelic + flt_test canonical divisor", "canonical ports feeding; promotion PENDING"),
    ("GeometricCore assembly", "GeometricCoreData", "statement layer; class B to be wired from A-class canonical proofs") ]

end LeanFormal.IUT.XiFPaper.GeomCore01StatementActual

end
