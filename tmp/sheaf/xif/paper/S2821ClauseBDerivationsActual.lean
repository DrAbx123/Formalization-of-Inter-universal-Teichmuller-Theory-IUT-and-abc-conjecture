import tmp.sheaf.xif.paper.S2817ClauseBAssemblyIndependentActual
import tmp.sheaf.xif.paper.S2798StableEverywhere37Actual
import tmp.sheaf.xif.paper.S2786E37PrimeIdealsActual
import tmp.sheaf.xif.paper.S2786PlaceBlockActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2817ClauseBAssemblyIndependentActual
open LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

local instance s2821GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2821ClauseBDerivationsActual

theorem S2821_vmod_eq :
    (S2786VmodBad : Set (NumberField.FinitePlace S2786Arithmetic.Fmod)) =
      ({S2786PlusPlace, S2786MinusPlace} :
        Set (NumberField.FinitePlace S2786Arithmetic.Fmod)) := by
  rfl

theorem S2821_plus_residue :
    residueCharacteristic S2786PlusPlace = 37 := by
  have h : S2786PlusPlace =
      (gaussianField37PlusPlace : NumberField.FinitePlace S2786Arithmetic.Fmod) := rfl
  rw [h]
  exact gaussianField37PlusPlace_residueCharacteristic

theorem S2821_minus_residue :
    residueCharacteristic S2786MinusPlace = 37 := by
  have h : S2786MinusPlace =
      (gaussianField37MinusPlace : NumberField.FinitePlace S2786Arithmetic.Fmod) := rfl
  rw [h]
  exact gaussianField37MinusPlace_residueCharacteristic

variable (S : SourceSignQuotientData S2786Arithmetic)
variable (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)

theorem S2821_comap_mem_vmod
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (w : NumberField.FinitePlace S2786Arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad) :
    NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S2786VmodBad := by
  rw [← S2786PlaceSelection_V_mod_bad, ← hV]
  exact hw

theorem S2821_comap_mem_plus_or_minus
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (w : NumberField.FinitePlace S2786Arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad) :
    NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w = S2786PlusPlace ∨
      NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w = S2786MinusPlace := by
  have hP : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
      S2786PlaceSelection.V_mod_bad := by
    rw [← hV]
    exact hw
  have hmem : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
      (S2786VmodBad : Set (NumberField.FinitePlace S2786Arithmetic.Fmod)) := by
    rw [← S2786PlaceSelection_V_mod_bad]
    exact hP
  have hmemF : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
      ({S2786PlusPlace, S2786MinusPlace} :
        Set (NumberField.FinitePlace S2786Arithmetic.Fmod)) := by
    rw [← S2821_vmod_eq]
    exact hmem
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmemF

theorem S2821_residueCharacteristic_comap_eq_37
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (w : NumberField.FinitePlace S2786Arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad) :
    residueCharacteristic (NumberFieldFinitePlace.comap (k := ℚ) w) = 37 := by
  have hwF := S2821_comap_mem_plus_or_minus S hV w hw
  have hwRes : residueCharacteristic
      (NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w) = 37 := by
    rcases hwF with h | h
    · rw [h]; exact S2821_plus_residue
    · rw [h]; exact S2821_minus_residue
  rw [NumberFieldFinitePlace.residueCharacteristic_comap (k := ℚ)]
  rw [← NumberFieldFinitePlace.residueCharacteristic_comap
    (k := S2786Arithmetic.Fmod) w]
  exact hwRes

theorem S2821_multiplicative
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad) :
    forall (w : NumberField.FinitePlace S2786Arithmetic.F),
      NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad →
        S2786Arithmetic.curve.HasMultiplicativeReductionAt w := by
  intro w hw
  exact S2798_multiplicative37 w (S2821_residueCharacteristic_comap_eq_37 S hV w hw)

theorem S2821_residue_coprime
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad) :
    forall (w : NumberField.FinitePlace S2786Arithmetic.F),
      NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic
            (NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w)) := by
  intro w hw
  have hwF := S2821_comap_mem_plus_or_minus S hV w hw
  rcases hwF with h | h
  · rw [h, S2821_plus_residue]
    norm_num [S2771FiveLabel]
  · rw [h, S2821_minus_residue]
    norm_num [S2771FiveLabel]

noncomputable def S2821ClauseB
    (hreal : forall (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw)) :
    SourceClauseB S2786Arithmetic S (S2813ClauseA S) :=
  S2817ClauseB S hV hreal (S2821_multiplicative S hV) (S2821_residue_coprime S hV)

#check S2821_multiplicative
#check S2821_residue_coprime
#check S2821ClauseB
#print axioms S2821ClauseB

end LeanFormal.IUT.XiFPaper.S2821ClauseBDerivationsActual
end
