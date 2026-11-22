import tmp.sheaf.xif.paper.S2703FourPlaceUseActual
import tmp.sheaf.xif.paper.S2703VbadSourceLinkActual

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

namespace LeanFormal.IUT.XiFPaper.S2706S2703BadQLowerActual

local instance s2706GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2706_five_residue :
    NumberFieldFinitePlace.residueCharacteristic
      (LeanFormal.IUT.XiFPaper.S2696VbadActual.S2696FourPlaceData.p5a
        LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual.S2703FourPlaceData) = 5 := by
  simpa [LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual.S2703FourPlaceData]
    using LeanFormal.IUT.XiFPaper.S2699TwoFivePlacesActual.S2699ResidueCharacteristicPlus

theorem S2706_2161_residue :
    NumberFieldFinitePlace.residueCharacteristic
      (LeanFormal.IUT.XiFPaper.S2696VbadActual.S2696FourPlaceData.p2161a
        LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual.S2703FourPlaceData) = 2161 := by
  simpa [LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual.S2703FourPlaceData]
    using LeanFormal.IUT.XiFPaper.S2698Two2161ResidueActual.S2698ResidueCharacteristicPlus

theorem S2706_two_log5_le_S2703BadQAbsLog (l : PrimeGeFive) :
    2 * Real.log (5 : ℝ) ≤
      LeanFormal.IUT.XiFPaper.S2703FourPlaceUseActual.S2703BadQAbsLog
        (LeanFormal.IUT.XiFPaper.S2703VbadSourceLinkActual.qVbad l
          LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual.S2703FourPlaceData) := by
  let D := LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual.S2703FourPlaceData
  let b5 : Bad (LeanFormal.IUT.XiFPaper.S2696VbadActual.S2696Selection l D) :=
    ⟨D.p5a, Or.inl rfl⟩
  let b2161 : Bad (LeanFormal.IUT.XiFPaper.S2696VbadActual.S2696Selection l D) :=
    ⟨D.p2161a, Or.inr (Or.inr (Or.inl rfl))⟩
  have hchar5 : NumberFieldFinitePlace.residueCharacteristic D.p5a = 5 := by
    simpa [D] using S2706_five_residue
  have hchar2161 : NumberFieldFinitePlace.residueCharacteristic D.p2161a = 2161 := by
    simpa [D] using S2706_2161_residue
  have hnePlaces : D.p5a ≠ D.p2161a := by
    intro h
    rw [h] at hchar5
    rw [hchar2161] at hchar5
    norm_num at hchar5
  have hne : b5 ≠ b2161 := by
    intro h
    exact hnePlaces (congrArg Subtype.val h)
  have hlt := LeanFormal.IUT.XiFPaper.S2703VbadSourceLinkActual.two_log5_lt_sourceBadQAbsLog_vbad
    l D b5 b2161 hne S2706_five_residue S2706_2161_residue
  simpa [LeanFormal.IUT.XiFPaper.S2703FourPlaceUseActual.S2703BadQAbsLog,
    LeanFormal.IUT.XiFPaper.S2703VbadSourceLinkActual.sourceBadQAbsLog_vbad]
    using le_of_lt hlt

#check S2706_two_log5_le_S2703BadQAbsLog
#print axioms S2706_two_log5_le_S2703BadQAbsLog

end LeanFormal.IUT.XiFPaper.S2706S2703BadQLowerActual
end
