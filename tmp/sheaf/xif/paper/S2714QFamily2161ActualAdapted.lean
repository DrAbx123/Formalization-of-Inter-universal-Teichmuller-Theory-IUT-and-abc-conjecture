import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2710GaussianResidueDegreeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2710GaussianResidueDegreeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2714QFamily2161ActualAdapted

local instance s2714GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2714_sectionFiniteLift_eq_self (l : PrimeGeFive)
    (p : NumberField.FinitePlace (S1280Arithmetic l).Fmod) :
    sectionFiniteLift (S2696SelectionTwo l) p = p := by
  have h1 : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod)
      (sectionFiniteLift (S2696SelectionTwo l) p) =
      sectionFiniteLift (S2696SelectionTwo l) p :=
    S1280_comap_eq_self l _
  have h2 : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod)
      (sectionFiniteLift (S2696SelectionTwo l) p) = p :=
    sectionFiniteLift_comap (S2696SelectionTwo l) p
  exact h1.symm.trans h2

theorem S2714_residueNormBase_section_2161 (l : PrimeGeFive) :
    residueNormBase
      (sectionFiniteLift (S2696SelectionTwo l) S2696GaussianPlace2161) = 2161 := by
  rw [S2714_sectionFiniteLift_eq_self]
  exact S2710_residueNormBase_S2696GaussianPlace

theorem S2714_localLog_2161 (l : PrimeGeFive)
    (b : Bad (S2696SelectionTwo l))
    (hb : b.1 = S2696GaussianPlace2161) :
    localLogMagnitude (badPlaceQCandidate (S2696SelectionTwo l) b) =
      |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)| := by
  obtain ⟨p, hp⟩ := b
  subst hb
  unfold badPlaceQProxy
  rw [localLogMagnitude_eq_order_mul_log,
    S2714_residueNormBase_section_2161,
    S2696GaussianPlace2161_residueCharacteristic]
  rw [abs_log_inv_pow_eq (N := (2161 : ℝ)) (by norm_num)]
  ring

#check S2714_sectionFiniteLift_eq_self
#check S2714_residueNormBase_section_2161
#check S2714_localLog_2161
#print axioms S2714_localLog_2161

end LeanFormal.IUT.XiFPaper.S2714QFamily2161ActualAdapted
end
