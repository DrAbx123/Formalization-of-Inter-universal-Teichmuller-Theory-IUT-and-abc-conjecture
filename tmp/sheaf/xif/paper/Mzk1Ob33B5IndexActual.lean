/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1NormDeterminantToolsActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineConstructionLinkActual
import tmp.sheaf.xif.paper.Mzk1PaperQPilotLineBundleSourceActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual

/-!
# Route B #3 step 3: finite-place index / rank-one SNF object

For a rank-one localized lattice the Smith normal form has a single invariant.
Given the mainline DVR generator datum, construct the actual place index as the
integer valuation of the generator, the relative index for D(H,O), and record
the exact missing general SNF input.  No named equality is consumed as proof.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1NormDeterminantToolsActual

variable {k : Type} [Field k] [NumberField k]

/-- Rank-one SNF data at a finite place: the single invariant is the integer
valuation of the DVR generator. -/
structure PlaceSNFData (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) where
  generatorData : LocalGeneratorData (k := k) I v
  index : Int
  index_eq : index = PaperOModuleActual.localValuation (k := k) v generatorData.generator

/-- Construct the rank-one SNF datum from the mainline generator datum. -/
noncomputable def placeSNFDataOfGenerator
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    (d : LocalGeneratorData (k := k) I v) : PlaceSNFData (k := k) I v where
  generatorData := d
  index := PaperOModuleActual.localValuation (k := k) v d.generator
  index_eq := rfl

theorem placeSNFDataOfGenerator_index
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    (d : LocalGeneratorData (k := k) I v) :
    (placeSNFDataOfGenerator (k := k) I v d).index =
      PaperOModuleActual.localValuation (k := k) v d.generator := rfl

/-- Relative finite-place index of D(H,O): the difference of the two generator
valuations (the rank-one SNF invariant of the relative determinant). -/
noncomputable def relativePlaceIndex
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v) : Int :=
  PaperOModuleActual.localValuation (k := k) v dH.generator -
    PaperOModuleActual.localValuation (k := k) v dO.generator

theorem relativePlaceIndex_eq
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v) :
    relativePlaceIndex dH dO =
      (placeSNFDataOfGenerator (k := k) H v dH).index -
        (placeSNFDataOfGenerator (k := k) O v dO).index := rfl

/-- Exact missing object for general higher-rank SNF/index.  Rank-one is constructed;
Mathlib has no canonical finite-index SNF object for a general sublattice. -/
def MissingGeneralPlaceSNF : Prop :=
  ∀ (I : LineBundle (k := k)) (v : NumberField.FinitePlace k),
    Nonempty (PlaceSNFData (k := k) I v)

section QPilot

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotLineBundleSourceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual bad-prime q-pilot source line bundle. -/
noncomputable def qPilotSourceLine : LineBundle (k := T.arithmetic.K) :=
  (qPilotLineBundleSourceOfBadPrimes T).qPilotLineBundle

/-- Exact per-place generator bridge for the actual q-pilot source: a DVR
generator of the localized line.  This is the missing object, not asserted. -/
def QPilotLocalGeneratorBridge (v : NumberField.FinitePlace T.arithmetic.K) : Prop :=
  Nonempty (LocalGeneratorData (k := T.arithmetic.K) (qPilotSourceLine T) v)

/-- Construct the rank-one SNF datum for the actual q-pilot source at a place
from a supplied generator datum. -/
noncomputable def qPilotPlaceSNFData
    (v : NumberField.FinitePlace T.arithmetic.K)
    (d : LocalGeneratorData (k := T.arithmetic.K) (qPilotSourceLine T) v) :
    PlaceSNFData (k := T.arithmetic.K) (qPilotSourceLine T) v :=
  placeSNFDataOfGenerator (k := T.arithmetic.K) (qPilotSourceLine T) v d

theorem qPilotPlaceSNFData_index
    (v : NumberField.FinitePlace T.arithmetic.K)
    (d : LocalGeneratorData (k := T.arithmetic.K) (qPilotSourceLine T) v) :
    (qPilotPlaceSNFData T v d).index =
      PaperOModuleActual.localValuation (k := T.arithmetic.K) v d.generator := rfl

/-- The exact missing generator existence for the actual q-pilot source. -/
def MissingQPilotLocalGenerator (v : NumberField.FinitePlace T.arithmetic.K) : Prop :=
  QPilotLocalGeneratorBridge T v

end QPilot

def b5IndexRows : List (String × String × String) :=
  [ ("PlaceSNFData", "rank-one SNF: one integer generator valuation", "CONSTRUCTED from LocalGeneratorData"),
    ("placeSNFDataOfGenerator", "generator datum -> SNF data", "CONSTRUCTED"),
    ("relativePlaceIndex", "per-place index of D(H,O) = val(xH)-val(xO)", "CONSTRUCTED"),
    ("relativePlaceIndex_eq", "difference of rank-one SNF invariants", "PROVED (rfl)"),
    ("MissingGeneralPlaceSNF", "general higher-rank SNF/index object absent in Mathlib", "PRECISE MISSING (not asserted)"),
    ("qPilotSourceLine", "actual bad-prime q-pilot source line bundle", "CONSTRUCTED (qpilot source)"),
    ("qPilotPlaceSNFData", "rank-one SNF datum from q-pilot generator", "CONSTRUCTED conditional on LocalGeneratorData"),
    ("MissingQPilotLocalGenerator", "actual per-place generator for q-pilot source", "PRECISE MISSING (not asserted)") ]

theorem b5IndexRows_length : b5IndexRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual
