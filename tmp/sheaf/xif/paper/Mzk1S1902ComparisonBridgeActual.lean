import tmp.sheaf.xif.paper.Mzk1S1902HullDataActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual

/-! # S1902 comparison region and concrete bridge (conditional height input)

## Scope / strength warning

`comparisonRegion` is taken to be the actual `s1902Hull`, so the
`regionVolume_le_normalizedWeight` slot with `D = 0` is essentially
`hull ≤ (1 + ε) * weight + hull`; all substantive content is in the explicit
height comparison.  Consequently this bridge data is **ABC-equivalent** in
strength: it must not be read as an independent proof of ABC. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902HullDataActual
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The comparison region is the actual S1902 hull; the shell point is the actual
q-pilot singleton point. Height comparison is the explicit parameter. -/
noncomputable def s1902EpsilonComparison (epsilon : Real) (heps : 0 < epsilon)
    (hheight : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * ((s1902HullData T).logVolume (s1902Hull T)).toReal) :
    Cor312EpsilonArithmeticComparisonV2 (s1902HullData T) epsilon where
  comparisonRegion := fun _ _ _ => s1902Hull T
  logShellPoint := fun _ _ _ => qPilotInThetaCarrier T
  logShellPoint_mem := by
    intro a b c
    exact qPilotInThetaCarrier_mem_hull T
  height_le_comparisonRegionVolume := hheight
  regionVolume_le_normalizedWeight := by
    refine ⟨(0 : Real), ?_⟩
    intro a b c _
    have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) :=
      arithmeticWeight_nonneg _
    have heps0 : 0 ≤ epsilon := le_of_lt heps
    nlinarith [mul_nonneg (by linarith : (0 : Real) ≤ 1 + epsilon) hw]

/-- Concrete S1902 bridge: conditional on the explicit height comparison input. -/
noncomputable def s1902Bridge
    (hheight : forall (epsilon : Real) (heps : 0 < epsilon),
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * ((s1902HullData T).logVolume (s1902Hull T)).toReal) :
    Cor312ToABCBridgeInterfaceV2 where
  carrier := S1902Carrier T
  hullData := s1902HullData T
  epsilonComparison := fun epsilon heps =>
    s1902EpsilonComparison T epsilon heps (hheight epsilon heps)

/-- The concrete bridge gives `ABCConjecture` (conditional only on the explicit
height comparison input). -/
theorem s1902Bridge_abc
    (hheight : forall (epsilon : Real) (heps : 0 < epsilon),
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * ((s1902HullData T).logVolume (s1902Hull T)).toReal) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjectureV2 (s1902Bridge T hheight)

#print axioms s1902Bridge_abc

end LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonBridgeActual
