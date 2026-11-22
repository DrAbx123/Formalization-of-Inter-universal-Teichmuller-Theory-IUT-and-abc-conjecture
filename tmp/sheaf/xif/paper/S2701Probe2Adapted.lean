import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2699GenericQPilotRayActual
import tmp.sheaf.xif.paper.S2702FourPlaceDataActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2699GenericQPilotRayActual
open LeanFormal.IUT.XiFPaper.S2702FourPlaceDataActual
local instance s2701GI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
noncomputable def S2701q (l : PrimeGeFive) (D : S2696FourPlaceData) :
    (p : NumberField.FinitePlace GaussianField) → p ∈ S2696Vbad D → Real :=
  fun p hp => |Real.log (badPlaceQProxy (S2696Selection l D) ⟨p, hp⟩)|
theorem S2701_five_mem (D : S2696FourPlaceData) : D.p5a ∈ S2696Vbad D := Or.inl rfl
theorem S2701_2161_mem (D : S2696FourPlaceData) : D.p2161a ∈ S2696Vbad D := Or.inr (Or.inr (Or.inl rfl))
theorem S2701_log_five_le (l : PrimeGeFive) (D : S2696FourPlaceData)
    (h : NumberFieldFinitePlace.residueCharacteristic D.p5a = 5) :
    Real.log 5 ≤ S2701q l D D.p5a (S2701_five_mem D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D) (⟨D.p5a, S2701_five_mem D⟩ : Bad (S2696Selection l D))
  have hchar : ((NumberFieldFinitePlace.residueCharacteristic D.p5a : Nat) : Real) = 5 := by
    rw [h]; norm_num
  rw [hchar] at hb
  simpa [S2701q] using hb
theorem S2701_log_2161_le (l : PrimeGeFive) (D : S2696FourPlaceData)
    (h : NumberFieldFinitePlace.residueCharacteristic D.p2161a = 2161) :
    Real.log 2161 ≤ S2701q l D D.p2161a (S2701_2161_mem D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D) (⟨D.p2161a, S2701_2161_mem D⟩ : Bad (S2696Selection l D))
  have hchar : ((NumberFieldFinitePlace.residueCharacteristic D.p2161a : Nat) : Real) = 2161 := by
    rw [h]; norm_num
  rw [hchar] at hb
  simpa [S2701q] using hb
noncomputable def S2701D : S2696FourPlaceData := S2702FourPlaceData
#check S2701D
#check (S2702Place5a_residueCharacteristic)
#check (S2696GaussianPlace2161_residueCharacteristic)
end
