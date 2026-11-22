import tmp.sheaf.xif.paper.S1939RootPacketDeterminantActual

noncomputable section
namespace S1939Consumer

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1939RootPacketDeterminantActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open scoped BigOperators

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

example (h : S1939FirstMissing T) :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1939Determinant T h) :=
  s1939_bridge T h

example (h : s1939HullScaleBound T) :
    (s1939Datum T h).determinant.procession.average = s1915A0 T :=
  s1939Datum_average T h

example :
    (s1939Procession T).average = s1915A0 T <-> |s1939BadLog T| <= 1 :=
  s1939_average_eq_a0_iff T

example (h : s1939HullScaleBound T) :
    -|Real.log ‖S1487Cand.q‖| <=
      OrigXiFSignedThetaHullLogVolume (s1939Datum T h) :=
  s1939_cor312 T h

example :
    S1939FirstMissing T <->
      (lStar l.value : Real) ^ 2 * |s1939BadLog T| <= s1939MeanSquare l :=
  s1939FirstMissing_iff_abs_bound T

example (h : s1939HullScaleBound T) :
    (s1939Determinant T h).hullLogVolume =
      (l.value : Real) * s1915A0 T + |s1939BadLog T| :=
  s1939Determinant_hullLogVolume_eq_a0 T h

#print axioms s1939_cor312
#print axioms s1939_exists_bridge_iff_hullScaleBound

end S1939Consumer