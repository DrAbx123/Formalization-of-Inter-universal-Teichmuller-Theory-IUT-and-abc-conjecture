import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.paper.IPLAPTActual
import tmp.sheaf.xif.paper.IPLAPTDataActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportConjugation

-- 
-- # Actual log-Kummer correspondence from source links and self-layer conjugation
-- 
-- Source: IUT III, Theorem 3.11, (ii), (iii); Proposition 3.10; IUT II,
-- Definition 4.9, (i). The log-Kummer correspondence consists of the inverse
-- Kummer isomorphisms between the vertically coric data and the Frobenioid-
-- theoretic data of the Hodge theater, with the x-mu layer on units and the
-- tensor packets of log-shells.
-- 
-- Construction: the actual self x-mu layer and self evaluation unit portion of
-- the core strip I.fPrimeStripAt 1 0 are transported along the actual source
-- F-prime-strip links I.fLinkAt. The transport is `SourceTimesMuKummerLayer.conjugate`
-- and `SourceEvaluationUnitPortion.conjugate`, which conjugate the actual units
-- actions and transport the actual times-mu isomorphisms. This yields, for
-- every m, an actual SourceTimesMuKummerLayer between the actual strips, hence
-- actual vertical Kummer arrows/card, and actual IPL data. No missing Kummer
-- layer is assumed, and no inequality/equality judgment is made.
-- 
-- WRITE-ONLY: no lake/lean.
-- 

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.FPrimeStrip
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

-- The common group of the actual log-Kummer layer: the canonical product
-- group of the core strip.
abbrev ActualKummerGroup : Type _ :=
  SelfGroup (I.fPrimeStripAt 1 0)

noncomputable def actualCoreSelfLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  selfKummerLayer (I.fPrimeStripAt 1 0)

noncomputable def actualCoreSelfEvaluation :
    SourceEvaluationUnitPortion (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  selfEvaluationUnitPortion (I.fPrimeStripAt 1 0)

-- Actual x-mu Kummer layer between arbitrary actual strips, obtained by
-- conjugating the core self layer along actual source strip links.
noncomputable def actualKummerLayerOf
    (upper lower : FPrimeStrip V)
    (sigma : FPrimeStripEquiv (I.fPrimeStripAt 1 0) upper)
    (tau : FPrimeStripEquiv (I.fPrimeStripAt 1 0) lower) :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I)) upper lower :=
  SourceTimesMuKummerLayer.conjugate (actualCoreSelfLayer (I := I)) sigma tau

-- Actual evaluation unit portion between arbitrary actual strips, obtained
-- by conjugating the core self unit portion along actual source links.
noncomputable def actualEvaluationUnitOf
    (upper lower : FPrimeStrip V)
    (sigma : FPrimeStripEquiv (I.fPrimeStripAt 1 0) upper)
    (tau : FPrimeStripEquiv (I.fPrimeStripAt 1 0) lower) :
    SourceEvaluationUnitPortion (ActualKummerGroup (I := I)) upper lower :=
  SourceEvaluationUnitPortion.conjugate (actualCoreSelfEvaluation (I := I)) sigma tau

-- ## Actual vertical links and Kummer arrows

def actualVerticalLink (m : Int) :
    FPrimeStripEquiv (I.fPrimeStripAt 1 m) (I.fPrimeStripAt 1 0) :=
  I.fLinkAt 1 m 1 0

noncomputable def actualVerticalKummerLayer (m : Int) :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 m) (I.fPrimeStripAt 1 0) :=
  actualKummerLayerOf (I := I) (I.fPrimeStripAt 1 m) (I.fPrimeStripAt 1 0)
    (I.fLinkAt 1 0 1 m) (FPrimeStripEquiv.refl (I.fPrimeStripAt 1 0))

noncomputable def actualKummerArrow (m : Int) :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 m) (I.fPrimeStripAt 1 0) :=
  sourceKummerArrowOfLayer (actualVerticalLink (I := I) m)
    (actualVerticalKummerLayer (I := I) m)

-- Actual vertical Kummer card of the 1-column log-Kummer correspondence.
noncomputable def actualVerticalKummerCard :
    SourceVerticalKummerCard (ActualKummerGroup (I := I)) I 1 where
  kummer m := actualKummerArrow (I := I) m

-- Actual 1-column log-Kummer correspondence object.
noncomputable def actualOneColumnLogKummer :
    OneColumnLogKummerData (ActualKummerGroup (I := I)) I where
  kummer := actualVerticalKummerCard (I := I)

-- ## Actual units and times-mu (log-shell) actions

def actualUnitsActionAt (m : Int) (v : V) :
    (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v →*
      MulAut ((I.fPrimeStripAt 1 m).Mon v)ˣ :=
  (I.fPrimeStripAt 1 m).unitsAction v

def actualTimesMuActionAt (m : Int) (v : V) :
    (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v →*
      MulAut (TimesMuQuotient ((I.fPrimeStripAt 1 m).Mon v)ˣ) :=
  (I.fPrimeStripAt 1 m).timesMuAction v

-- ## Actual IPL data from actual links and conjugated layers

def iplIntermediateStrip : FPrimeStrip V := I.fPrimeStripAt 1 0
def iplGauStrip : FPrimeStrip V := I.fPrimeStripAt 1 1
def iplEnvStrip : FPrimeStrip V := I.fPrimeStripAt 1 0
def iplCoricEnvStrip : FPrimeStrip V := I.fPrimeStripAt 0 0
def iplQPilotStrip : FPrimeStrip V := I.fPrimeStripAt 1 0

def actualLowerHorizontal1 :
    FPrimeStripEquiv (iplGauStrip (I := I)) (iplIntermediateStrip (I := I)) :=
  I.fLinkAt 1 1 1 0

def actualLowerHorizontal2 :
    FPrimeStripEquiv (iplEnvStrip (I := I)) (iplGauStrip (I := I)) :=
  I.fLinkAt 1 0 1 1

def actualKummerLink :
    FPrimeStripEquiv (iplEnvStrip (I := I)) (iplCoricEnvStrip (I := I)) :=
  I.fLinkAt 1 0 0 0

def actualEvaluationLink :
    FPrimeStripEquiv (iplCoricEnvStrip (I := I)) (iplQPilotStrip (I := I)) :=
  I.fLinkAt 0 0 1 0

noncomputable def actualIPLKummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (iplEnvStrip (I := I)) (iplCoricEnvStrip (I := I)) :=
  actualKummerLayerOf (I := I) (iplEnvStrip (I := I)) (iplCoricEnvStrip (I := I))
    (FPrimeStripEquiv.refl (I.fPrimeStripAt 1 0))
    (I.fLinkAt 1 0 0 0)

noncomputable def actualIPLEvaluationUnit :
    SourceEvaluationUnitPortion (ActualKummerGroup (I := I))
      (iplCoricEnvStrip (I := I)) (iplQPilotStrip (I := I)) :=
  actualEvaluationUnitOf (I := I) (iplCoricEnvStrip (I := I)) (iplQPilotStrip (I := I))
    (I.fLinkAt 1 0 0 0) (I.fLinkAt 1 0 1 0)

noncomputable def actualIPLKummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (iplEnvStrip (I := I)) (iplCoricEnvStrip (I := I)) :=
  sourceKummerArrowOfLayer (actualKummerLink (I := I))
    (actualIPLKummerLayer (I := I))

noncomputable def actualIPLEvaluationArrow :
    SourceEvaluationArrow (ActualKummerGroup (I := I))
      (iplCoricEnvStrip (I := I)) (iplQPilotStrip (I := I)) :=
  sourceEvaluationArrowOfUnitPortion (actualEvaluationLink (I := I))
    (actualIPLEvaluationUnit (I := I))

noncomputable def actualIPLInputLink :
    FPrimeStripEquiv (iplIntermediateStrip (I := I)) (iplQPilotStrip (I := I)) :=
  FPrimeStripEquiv.trans (FPrimeStripEquiv.symm (actualLowerHorizontal1 (I := I)))
    (FPrimeStripEquiv.trans (FPrimeStripEquiv.symm (actualLowerHorizontal2 (I := I)))
      (FPrimeStripEquiv.trans (actualIPLKummerArrow (I := I)).stripIso
        (actualIPLEvaluationArrow (I := I)).stripIso))

noncomputable def actualIPLData :
    IPLActual (G := ActualKummerGroup (I := I))
      (iplIntermediateStrip (I := I)) (iplGauStrip (I := I))
      (iplEnvStrip (I := I)) (iplCoricEnvStrip (I := I)) (iplQPilotStrip (I := I)) where
  lowerHorizontal1 := actualLowerHorizontal1 (I := I)
  lowerHorizontal2 := actualLowerHorizontal2 (I := I)
  kummer := actualIPLKummerArrow (I := I)
  evaluation := actualIPLEvaluationArrow (I := I)
  inputLink := actualIPLInputLink (I := I)
  factorization := rfl

#check ActualKummerGroup
#check actualKummerLayerOf
#check actualEvaluationUnitOf
#check actualVerticalLink
#check actualVerticalKummerLayer
#check actualKummerArrow
#check actualVerticalKummerCard
#check actualOneColumnLogKummer
#check actualUnitsActionAt
#check actualTimesMuActionAt
#check actualIPLKummerLayer
#check actualIPLEvaluationUnit
#check actualIPLData

end LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource

end