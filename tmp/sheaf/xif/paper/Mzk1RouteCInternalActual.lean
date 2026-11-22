/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import Mathlib.Tactic

/-! # A855/A856/A858: Route C internal layer (Frey data, delta, external props, bridge) -/

/- External upstream theorems are treated as PROVEN (not ported here): they appear only as
explicit `Prop` hypotheses.  Our own content: FreyData with exact discriminant identity,
the delta interface, the Frey log dictionary, and the arithmetic bridge to Szpiro6Shape.

G2: `ModularParameterizationDegree` = structure with level/degree/isogeny Prop fields;
    `RibetTakahashiDelta` = N_E/N_f as data; `PastenDeltaBound` = explicit external Prop.
G3: `FreyLogDictionary`: log q = 2 log delta, logdf = log N (hypothesis, not proved).
G4: bridge `szpiro6_of_routeC` : PastenDeltaBound + dictionary => Szpiro6Shape (2C).
Frey curve data: `freyDisc a b c = 16*(a*b*c)^2` (exact integer identity, rfl);
conductor = rad(abc) is recorded as a data field with its defining Prop (PENDING). -/

noncomputable section

open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual

namespace LeanFormal.IUT.XiFPaper.Mzk1RouteCInternalActual

structure FreyData where
  a : ℤ
  b : ℤ
  c : ℤ
  isAbc : a + b = c
  conductor : ℕ
  conductor_isRadical : Prop

def freyDisc (a b c : ℤ) : ℤ := 16 * (a * b * c) ^ 2

theorem freyDisc_eq (a b c : ℤ) : freyDisc a b c = 16 * (a * b * c) ^ 2 := rfl

structure ModularParameterizationDegree where
  level : ℕ
  degree : ℕ
  degree_pos : 0 < degree
  isIsogenyDegree : Prop

def ribetTakahashiDelta (N_E N_f : ℕ) : ℕ := N_E / N_f

def PastenDeltaBound (logDelta logN C epsilon : ℝ) : Prop :=
  logDelta ≤ (2 + epsilon) * logN + C

def ModularityHypothesis (E : Type) : Prop := Nonempty E → Nonempty E
def RibetLoweringHypothesis (N_E N_f : ℕ) : Prop := 0 < N_E → 0 < N_f → True

def FreyLogDictionary (logq logDelta logdf logN : ℝ) : Prop :=
  logq = 2 * logDelta ∧ logdf = logN

theorem szpiro6_of_routeC {logDelta logN logq logdf C epsilon : ℝ}
    (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (hN : 0 ≤ logN)
    (hbound : PastenDeltaBound logDelta logN C epsilon)
    (hdict : FreyLogDictionary logq logDelta logdf logN) :
    Szpiro6Shape logq logdf (2 * C) := by
  obtain ⟨hq, hdf⟩ := hdict
  unfold Szpiro6Shape PastenDeltaBound at *
  rw [hq, hdf]
  have hεN : epsilon * logN ≤ 1 * logN :=
    mul_le_mul_of_nonneg_right heps1 hN
  nlinarith

def routeCInternalRows : List (String × String × String) :=
  [ ("freyDisc", "16*(a*b*c)^2 exact identity", "PROVED (rfl)") ,
    ("FreyData.conductor_isRadical", "N = rad(abc)", "DATA (PENDING) ") ,
    ("ModularParameterizationDegree", "level/degree/pos/isogenyProp", "DEF") ,
    ("ribetTakahashiDelta", "N_E/N_f", "DEF") ,
    ("PastenDeltaBound", "logDelta <= (2+eps)logN + C", "EXTERNAL PROP") ,
    ("ModularityHypothesis/RibetLoweringHypothesis", "external upstream theorem placeholders", "PROP PARAMS") ,
    ("FreyLogDictionary", "logq=2logDelta, logdf=logN", "HYPOTHESIS") ,
    ("szpiro6_of_routeC", "external delta bound + dict => Szpiro6 (2C)", "PROVED") ]

theorem routeCInternalRows_length : routeCInternalRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1RouteCInternalActual
