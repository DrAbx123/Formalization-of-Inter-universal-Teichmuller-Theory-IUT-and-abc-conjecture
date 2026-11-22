/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5HproductGeneralAttemptActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1P1IdealMapPowerGeneralActual
import tmp.sheaf.xif.paper.Mzk1Ob33ArchMetricActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapLogActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapOfResidueOneActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneSinglePointActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneBothSidesActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineFromBadPrimeSourceActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapOfResidueOneActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual

variable {l : PrimeGeFive}
variable {k : Type} [Field k] [NumberField k]
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

structure FiniteIndexData
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v) where
  eq : finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO =
    relativeDetLog (k := T.arithmetic.K) (badPrimeSource T).qPilotLineBundle O
theorem finiteIndexExpansion_of_data
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (D : FiniteIndexData T O s dH dO) : FiniteIndexExpansion T O s dH dO := D.eq


end LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataActual
