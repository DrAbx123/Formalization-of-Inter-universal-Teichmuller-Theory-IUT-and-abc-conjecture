/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.Tactic

/-! # A2 node03: remaining geometric V/epsilon fields -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceVFieldsActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- The V/epsilon tuple components of Definition 3.1(e)-(f), typed against
the fixed source `S`. -/
structure A2Node03SourceVFieldsData (S : SourceSignQuotientData A) where
  V : Set (NumberFieldPlace A.K)
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ p, p ∈ V_mod_bad → Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection A.Fmod A.K
  V_eq_section : V = V_section.selected
  V_mod_bijection :
    NumberFieldPlace A.Fmod ≃ {v : NumberFieldPlace A.K // v ∈ V}
  V_place_comap :
    ∀ v : {v : NumberFieldPlace A.K // v ∈ V},
      NumberFieldPlace.comap (k := A.Fmod) v.1 = V_mod_bijection.symm v
  epsilon : Iut.OrbicurveBoundaryCusp S.cK

noncomputable def sourceSignQuotientDataWithVFields
    (S : SourceSignQuotientData A)
    (D : A2Node03SourceVFieldsData S) :
    SourceSignQuotientData A :=
  { S with
    V := D.V
    V_mod_bad := D.V_mod_bad
    V_mod_bad_odd_residue_characteristic := D.V_mod_bad_odd_residue_characteristic
    V_mod_bad_nonempty := D.V_mod_bad_nonempty
    V_section := D.V_section
    V_eq_section := D.V_eq_section
    V_mod_bijection := D.V_mod_bijection
    V_place_comap := D.V_place_comap
    epsilon := D.epsilon }

def A2Node03SourceVFieldsRequired
    (S : SourceSignQuotientData A) : Prop :=
  Nonempty (A2Node03SourceVFieldsData S)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceVFieldsActual
