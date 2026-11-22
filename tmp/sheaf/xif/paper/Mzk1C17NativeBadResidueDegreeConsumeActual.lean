/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17NativeBadResidueFieldGapActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueWeightChainActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadResidueDegreeConsumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadResidueFieldGapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueWeightChainActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem localResidueDegree_nativeBad_eq_one_of_missing
    (b : Bad (nativePlaceSelection T))
    (hmissing : MissingNativeBadResidueFieldEquiv T) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1 :=
  localResidueDegree_eq_one_of_residueFieldEquiv T b (hmissing b)


end LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadResidueDegreeConsumeActual
