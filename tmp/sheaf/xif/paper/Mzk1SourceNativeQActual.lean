/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual
import tmp.sheaf.xif.paper.Mzk1QPilotPlaceDegreeActual
import tmp.sheaf.xif.paper.Mzk1DegreeSumActual
import Mathlib.Tactic

/-! # R29ah / task-114: GAP-SOURCE-NATIVE-Q for the S1487 canonical case -/

/-
| field | value |
|---|---|
| Status | PARTIAL/green: S1487 canonical contract qParameter identified definitionally with `‖S1487Cand.q‖`; source bad-q sum identified with one-place abs log under uniqueness of the native bad index and an explicit per-place value bridge |
| Reuse | `S1487OQPilotScalarEqualityActual:520 S1487FaithfulSourceData`（qParameter = fun _ => ‖S1487Cand.q‖, badPlaces = PUnit）; `:400 S1487SourceData`; `Mzk1QPilotPlaceDegreeActual`（nativeBadQAbsLogSum）; `Mzk1DegreeSumActual`（degree sum） |
| GAP | GAP-SOURCE-NATIVE-Q（general）：index map badPlaces ↔ Bad (nativePlaceSelection T) and per-place `qParameter b = ‖qVFamily b .q‖` not constructed from geometry; only the canonical S1487 value + conditional sum bridge are proved |
| 纪律 | no sorry/axiom; conditional identification is explicit; no Prop placeholder for the data |
-/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1SourceNativeQActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotPlaceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1DegreeSumActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

variable {l : PrimeGeFive}

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. S1487 canonical contract qParameter -/

/-- The S1487 canonical q-parameter is definitionally the Gaussian q magnitude. -/
theorem S1487_qParameter_eq_norm (b : PUnit) :
    (S1487FaithfulSourceData (l := l)).reduction.qParameter b =
      ‖S1487Cand.q‖ := rfl

/-- The one-place source bad-q absolute log is `|log ‖S1487Cand.q‖|`. -/
theorem S1487_badQAbsLog_eq_abs_log_norm (b : PUnit) :
    |Real.log ((S1487FaithfulSourceData (l := l)).reduction.qParameter b)| =
      |Real.log ‖S1487Cand.q‖| := by
  rw [S1487_qParameter_eq_norm]

/-! ## 2. Native qVFamily norm identification interface -/

/-- Explicit per-place identification for the canonical S1487 case: the contract
q-parameter absolute log equals the native qVFamily default-norm absolute log. -/
def S1487NativeQIdentification
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) : Prop :=
  |Real.log ((S1487FaithfulSourceData (l := l)).reduction.qParameter PUnit.unit)| =
    |Real.log (qVFamDefaultNorm T b)|

/-- Under the per-place identification, the S1487 contract q-parameter absolute log
is the native qVFamily default-norm absolute log (definitional reduction). -/
theorem S1487_abs_log_eq_qVFamDefaultNorm_abs_log
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T))
    (h : S1487NativeQIdentification (l := l) T b) :
    |Real.log ((S1487FaithfulSourceData (l := l)).reduction.qParameter PUnit.unit)| =
      |Real.log (qVFamDefaultNorm T b)| :=
  h

/-! ## 3. Source bad-q sum = native bad-q sum (single-index condition) -/

/-- **Canonical S1487 sum bridge**: if the native bad index is a singleton and the
per-place identification holds, the contract source bad-q absolute log equals
`nativeBadQAbsLogSum` (the task-99/105 degree-sum input). -/
theorem S1487_sourceBadQAbsLog_eq_nativeBadQAbsLogSum
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [Unique (Bad (nativePlaceSelection T))]
    (hsrc : OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l)) =
      |Real.log (qVFamDefaultNorm T (default : Bad (nativePlaceSelection T)))|) :
    OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l)) =
      nativeBadQAbsLogSum T := by
  have hsum : nativeBadQAbsLogSum T =
      |Real.log (qVFamDefaultNorm T (default : Bad (nativePlaceSelection T)))| := by
    classical
    unfold nativeBadQAbsLogSum
    rw [Finset.sum_eq_single (default : Bad (nativePlaceSelection T))]
    · intro b _ hb
      exact absurd (Subsingleton.elim b default) hb
    · intro hbad
      exact absurd (Finset.mem_univ default) hbad
  rw [hsrc, hsum]
def sourceNativeQRows : List (String × String) :=
  [ ("S1487_qParameter_eq_norm", "S1487 canonical qParameter = ||S1487Cand.q|| (rfl)") ,
    ("S1487_badQAbsLog_eq_abs_log_norm", "per-place abs log value (PROVED)") ,
    ("S1487NativeQIdentification", "explicit per-place bridge predicate") ,
    ("S1487_abs_log_eq_qVFamDefaultNorm_abs_log", "bridge predicate unfolds (PROVED)") ,
    ("S1487_sourceBadQAbsLog_eq_nativeBadQAbsLogSum", "singleton-index sum bridge (PROVED conditionally)") ,
    ("GAP-SOURCE-NATIVE-Q", "general index map and qParameter = ||qVFamily q|| not constructed") ]

theorem sourceNativeQRows_length : sourceNativeQRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SourceNativeQActual