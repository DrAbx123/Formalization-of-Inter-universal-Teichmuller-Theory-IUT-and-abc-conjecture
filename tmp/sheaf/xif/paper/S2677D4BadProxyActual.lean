import tmp.sheaf.xif.paper.S1527OOrderEqualityActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4TateQIdentification

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

namespace LeanFormal.IUT.XiFPaper.S2677D4BadProxyActual

variable (l : PrimeGeFive)

def S2677w0 : NumberField.FinitePlace (S1280Arithmetic l).F :=
  S1280Place l

theorem S2677_comap_w0 :
    NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) (S2677w0 l) =
      S1280Place l :=
  S1280_comap_eq_self l (S2677w0 l)

theorem S2677_hw0 :
    NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) (S2677w0 l) ∈
      (S1280Selection l).V_mod_bad := by
  rw [S2677_comap_w0]
  rw [S1280Selection_V_mod_bad]
  exact Set.mem_singleton _

theorem S2677_proxy_value
    (C : LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization.BadPlaceTateUniformizationCards
      (S1280Selection l))
    (h : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.TateQIdentificationStatement
      (S1280Selection l) C)
    (b : Bad (S1280Selection l)) :
    badPlaceQProxy (S1280Selection l) b =
      ((5 : ℝ)⁻¹) ^
        (C.parameter (S2677w0 l) (S2677_hw0 l)).order := by
  have hval := badPlaceQProxy_eq_of_identification
    (P := S1280Selection l) C h (S2677w0 l) (S2677_hw0 l)
  have hb : (⟨NumberFieldFinitePlace.comap (S2677w0 l), S2677_hw0 l⟩ :
      Bad (S1280Selection l)) = b := by
    apply Subtype.ext
    change NumberFieldFinitePlace.comap (S2677w0 l) = b.1
    rw [S2677_comap_w0]
    exact (S1527_bad_val_eq l b).symm
  rw [← hb, hval, S2677_comap_w0, S1280Place_residueCharacteristic]
  norm_num

theorem S2677_abs_log_value
    (C : LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization.BadPlaceTateUniformizationCards
      (S1280Selection l))
    (h : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.TateQIdentificationStatement
      (S1280Selection l) C)
    (b : Bad (S1280Selection l)) :
    |Real.log (badPlaceQProxy (S1280Selection l) b)| =
      ((C.parameter (S2677w0 l) (S2677_hw0 l)).order : ℝ) * Real.log 5 := by
  rw [S2677_proxy_value l C h b]
  exact S1527_abs_log_inv_five_pow _
    (LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceQCandidate.order_pos
      (C.parameter (S2677w0 l) (S2677_hw0 l)))

#check S2677_proxy_value
#check S2677_abs_log_value

#check S2677w0
#check S2677_comap_w0
#check S2677_hw0

end LeanFormal.IUT.XiFPaper.S2677D4BadProxyActual
end
