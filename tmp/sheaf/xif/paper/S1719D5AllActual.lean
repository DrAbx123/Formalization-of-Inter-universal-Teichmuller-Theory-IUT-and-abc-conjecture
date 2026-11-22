import tmp.sheaf.xif.paper.S1717PlaceSevenD5Actual
import tmp.sheaf.xif.paper.S1712OddResidueActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1715SourceTorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual

namespace LeanFormal.IUT.XiFPaper.S1719D5AllActual

noncomputable def S1719PlaceFiveData (l : PrimeGeFive) (h5 : l.value ≠ 5) :
    S1717D5PlaceData l where
  place := S1687PlaceAboveFive
  splitMultiplicative := S1687Split_of_rational S1711RationalSplitAtFive
  odd_residueCharacteristic := S1712Odd
  residueCharacteristic := 5
  residueCharacteristic_eq := by
    have h := NumberFieldFinitePlace.residueCharacteristic_comap
      (k := ℚ) (K := S1687Field) S1687PlaceAboveFive
    rw [S1687PlaceAboveFive_comap] at h
    rw [← h, S1712ConcreteFivePlace_residueCharacteristic]
  lTorsionCompatible :=
    (Nat.coprime_primes l.prime Nat.prime_five).mpr h5

noncomputable def S1719PlaceSevenData (l : PrimeGeFive) (h7 : l.value ≠ 7) :
    S1717D5PlaceData l where
  place := S1687PlaceAboveSeven
  splitMultiplicative := S1717SplitAtPlaceSeven
  odd_residueCharacteristic := S1717OddResidue_placeAboveSeven
  residueCharacteristic := 7
  residueCharacteristic_eq := S1717ResidueCharacteristic_placeAboveSeven.symm
  lTorsionCompatible :=
    (Nat.coprime_primes l.prime Nat.prime_seven).mpr h7

noncomputable def S1719D5ClauseAll (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) :
    SourceTorsionClause.{0, 0, 0} l := by
  by_cases h5 : l.value = 5
  · have h7 : l.value ≠ 7 := by
      intro h
      exact (by norm_num : (5 : Nat) ≠ 7) (h5.symm.trans h)
    exact S1717SourceTorsionClause l (S1719PlaceSevenData l h7) hI
  · exact S1715SourceTorsionClause l hI h5


#print axioms S1719D5ClauseAll

end LeanFormal.IUT.XiFPaper.S1719D5AllActual
