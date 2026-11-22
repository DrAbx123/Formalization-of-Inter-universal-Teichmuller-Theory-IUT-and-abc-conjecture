/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.flt.FLT.DedekindDomain.Completion.BaseChange
import tmp.sheaf.xif.paper.Mzk1P3WeightDegreeOneActual
import tmp.sheaf.xif.paper.Mzk1P3AgreeFLTActual
import Mathlib.Tactic

/-!
# P6-E5: UNRAM/RESIDUE bridge (FLT completion data -> degree one -> weight one)

Status: CONDITIONAL. This file imports the FLT Completion/BaseChange module,
records the :718/:751 comparison theorems, and instantiates the project
relative-degree one chain. Global e=1/f=1 remain arithmetic inputs.
-/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual

namespace LeanFormal.IUT.XiFPaper.Mzk1C17UnramResidueBridgeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Project-level chain: global e=f=1 at the section place implies relative
completion degree one. -/
theorem relativeCompletionDegree_eq_one_of_unram_residue
    (b : Bad (nativePlaceSelection T))
    (he : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hf : relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    relativeCompletionDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1 :=
  (relativeCompletionDegree_eq_one_iff (k := T.arithmetic.Fmod) (K := T.arithmetic.K)
    (nativeBadToKPlace T b)).mpr ⟨he, hf⟩

/-- Full UNRAM/RESIDUE bridge: FINITE + AGREE + e=1 + f=1 => nativeBadLocalWeight=1. -/
theorem nativeBadLocalWeight_eq_one_of_unram_residue_bridge
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (he : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hf : relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 :=
  nativeBadLocalWeight_eq_one_of_unram_residue (l := l) T b hfinite hagree he hf

/- FLT :718 comparison theorem (local = global inertia degree). -/
#check IsDedekindDomain.HeightOneSpectrum.adicCompletion.inertiaDeg_eq_inertiaDeg

/- FLT :751 comparison theorem (e * f = finrank of completions). -/
#check IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank

def bridgeRows : List (String × String × String) :=
  [ ("relativeCompletionDegree_eq_one_of_unram_residue", "e=f=1 => degree=1", "PROVED conditional"),
    ("nativeBadLocalWeight_eq_one_of_unram_residue_bridge", "e=f=1+finite+agree => weight=1", "PROVED conditional"),
    ("FLT inertiaDeg_eq_inertiaDeg", "BaseChange:718", "IMPORTED/check"),
    ("FLT ramificationIdx_mul_inertiaDeg_eq_finrank", "BaseChange:751", "IMPORTED/check") ]
theorem bridgeRows_length : bridgeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C17UnramResidueBridgeActual
