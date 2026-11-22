import tmp.sheaf.xif.paper.S2902CoreWithQMinimalActual
import tmp.sheaf.xif.paper.S2901CuspBoundaryInputActual
import tmp.sheaf.xif.paper.S2895KSideInputActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2902CoreWithQMinimalActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2910VDataInputActual

/-- Minimal V-side input: places, section, and the bijection/comap data. -/
structure S2910VInput where
  V : Set (NumberFieldPlace S2847A6.K)
  V_mod_bad : Set (NumberField.FinitePlace S2847A6.Fmod)
  V_mod_bad_odd_residue_characteristic :
    forall p, p ∈ V_mod_bad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection S2847A6.Fmod S2847A6.K
  V_eq_section : V = V_section.selected
  V_mod_bijection :
    NumberFieldPlace S2847A6.Fmod ≃ {v : NumberFieldPlace S2847A6.K // v ∈ V}
  V_place_comap :
    forall v : {v : NumberFieldPlace S2847A6.K // v ∈ V},
      NumberFieldPlace.comap (k := S2847A6.Fmod) v.1 =
        (V_mod_bijection.symm v)

/-- Extract the V-side package from S2902Inputs. -/
noncomputable def S2910VInput.ofS2902
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2844D6F6BaseChangeActual.K)}
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    {W : S2870QuotientWitnessData S2882A6Q hQ A}
    (I : S2902Inputs hQ A W) : S2910VInput where
  V := I.V
  V_mod_bad := I.V_mod_bad
  V_mod_bad_odd_residue_characteristic := I.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := I.V_mod_bad_nonempty
  V_section := I.V_section
  V_eq_section := I.V_eq_section
  V_mod_bijection := I.V_mod_bijection
  V_place_comap := I.V_place_comap

/-- Replace the V-side fields of S2902Inputs by a packaged S2910VInput. -/
noncomputable def S2910WithV
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2844D6F6BaseChangeActual.K)}
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    {W : S2870QuotientWitnessData S2882A6Q hQ A}
    (I : S2902Inputs hQ A W) (V : S2910VInput) :
    S2902Inputs hQ A W :=
  { I with
    V := V.V
    V_mod_bad := V.V_mod_bad
    V_mod_bad_odd_residue_characteristic := V.V_mod_bad_odd_residue_characteristic
    V_mod_bad_nonempty := V.V_mod_bad_nonempty
    V_section := V.V_section
    V_eq_section := V.V_eq_section
    V_mod_bijection := V.V_mod_bijection
    V_place_comap := V.V_place_comap }

#check S2910VInput
#check S2910VInput.ofS2902
#check S2910WithV
#print axioms S2910VInput.ofS2902

end LeanFormal.IUT.XiFPaper.S2910VDataInputActual
end