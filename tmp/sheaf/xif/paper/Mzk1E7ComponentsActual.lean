/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1E7ReductionActual
import Mathlib.Tactic

/-! # A861: E7 components - provable parts and external fields -/

/- Four components of E7-GAP as explicit Props over reals:
* FaltingsUpperBound: hF <= (1+eps)*logN + C;
* NeronPeriodLowerBound: volE >= N^(-(1+eps)) - C;
* PeterssonIdentity (cleared): deg * (c^2*volE) = 4*pi^2*phiStar; the divided form is proved
  under nonzero side conditions;
* OptimalQuotient: explicit Prop field (external).
Provable here: the algebra cleared -> divided, and the data wiring into E7Data.
The arithmetic bridge to Szpiro6Shape is Mzk1RouteCInternalActual.szpiro6_of_routeC.
No sorry/axiom. -/

noncomputable section

open LeanFormal.IUT.XiFPaper.Mzk1E7ReductionActual

namespace LeanFormal.IUT.XiFPaper.Mzk1E7ComponentsActual

def FaltingsUpperBound (hF logN eps C : ℝ) : Prop := hF ≤ (1 + eps) * logN + C

def NeronPeriodLowerBound (volE N eps C : ℝ) : Prop := volE ≥ N ^ (-(1 + eps)) - C

def PeterssonIdentity (deg phiStar c volE : ℝ) : Prop :=
  deg * (c ^ 2 * volE) = 4 * Real.pi ^ 2 * phiStar

def PeterssonIdentityDivided (deg phiStar c volE : ℝ) : Prop :=
  deg = 4 * Real.pi ^ 2 * phiStar / (c ^ 2 * volE)

theorem petersson_divided_of_cleared {deg phiStar c volE : ℝ}
    (hc : c ≠ 0) (hv : volE ≠ 0) (h : PeterssonIdentity deg phiStar c volE) :
    PeterssonIdentityDivided deg phiStar c volE := by
  unfold PeterssonIdentity at h
  unfold PeterssonIdentityDivided
  field_simp [hc, hv]
  linarith

structure E7ComponentProps where
  faltings : Prop
  petersson : Prop
  neron : Prop
  optimal : Prop

def e7DataOfComponents (level degree : ℕ) (hpos : 0 < degree)
    (C : E7ComponentProps) : E7Data :=
  { level := level, degree := degree, degree_pos := hpos,
    faltingsUpperBound := C.faltings, peterssonIdentity := C.petersson,
    neronPeriodLowerBound := C.neron, optimalQuotient := C.optimal }

theorem e7Gap_of_components (level degree : ℕ) (hpos : 0 < degree)
    (C : E7ComponentProps)
    (hjoint : jointPackage (e7DataOfComponents level degree hpos C))
    (hE7 : E7Statement (e7DataOfComponents level degree hpos C)) :
    E7GapStatement (e7DataOfComponents level degree hpos C) :=
  ⟨hE7, hjoint⟩
def componentRows : List (String × String × String) :=
  [ ("FaltingsUpperBound", "hF <= (1+eps)logN + C", "PROP (external)") ,
    ("NeronPeriodLowerBound", "volE >= N^(-(1+eps)) - C", "PROP (external)") ,
    ("PeterssonIdentity", "deg*(c^2*volE) = 4 pi^2 phiStar", "PROP (external)") ,
    ("petersson_divided_of_cleared", "cleared => divided form", "PROVED") ,
    ("OptimalQuotient", "optimal quotient Prop field", "EXTERNAL") ,
    ("e7Gap_of_components", "components + E7Statement => E7GapStatement", "PROVED (logic)") ]

theorem componentRows_length : componentRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E7ComponentsActual
