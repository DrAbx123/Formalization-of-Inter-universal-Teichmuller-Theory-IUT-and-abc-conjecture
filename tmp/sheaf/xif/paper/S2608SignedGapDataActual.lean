import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction

noncomputable section
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2608SignedGapDataActual

universe u

/-- Signed gap-1 input package: weight comparison plus the correct H1 valuation
input, with signed region volume on the right. -/
structure SignedGap1Data (X : Type u) where
  region : Nat -> Nat -> Nat -> Set X
  logVolume : Set X -> ENNReal
  eps : Real
  heps : 0 <= eps
  hval : forall a b c : Nat, IsABCTriple a b c ->
    forall q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
      max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps
  hweightvol : forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      (logVolume (region a b c)).toReal

def SignedGap1Data.conclusion {X : Type u} (D : SignedGap1Data X) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcRationalPoint a c) <=
      (1 + D.eps) * (D.logVolume (D.region a b c)).toReal

/-- Signed gap-2 input package: split, scaled-unit bound, singleton finiteness,
and the singleton point bound, all with signed log-volume. -/
structure SignedGap2Data (X : Type u) where
  region : Nat -> Nat -> Nat -> Set X
  scaledUnit : Nat -> Nat -> Nat -> Set X
  singleton : Nat -> Nat -> Nat -> Set X
  hull : Set X
  logVolume : Set X -> ENNReal
  eps : Real
  D0 : Real
  D1 : Real
  hD0 : 0 <= D0
  hsplit : forall a b c : Nat, IsABCTriple a b c ->
    logVolume (region a b c) <=
      logVolume (scaledUnit a b c) + logVolume (singleton a b c)
  hunitScaled : forall a b c : Nat, IsABCTriple a b c ->
    logVolume (scaledUnit a b c) <=
      logVolume hull + ENNReal.ofReal D0
  hptfin : forall a b c : Nat, IsABCTriple a b c ->
    logVolume (singleton a b c) < ⊤
  hpoint : forall a b c : Nat, IsABCTriple a b c ->
    (logVolume (singleton a b c)).toReal <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1

#check SignedGap1Data
#check SignedGap1Data.conclusion
#check SignedGap2Data

end LeanFormal.IUT.XiFPaper.S2608SignedGapDataActual
end