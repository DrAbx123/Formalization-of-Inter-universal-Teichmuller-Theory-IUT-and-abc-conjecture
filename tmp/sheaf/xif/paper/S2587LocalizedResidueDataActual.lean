import tmp.sheaf.xif.paper.S2574LocalizedP12Actual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2586PrimeMaximalActual
import tmp.sheaf.xif.paper.S2574LocalizedModelActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual

open LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2586PrimeMaximalActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

lemma S2574f_natDegree : S2574f.natDegree = 12 := by
  rw [S2574f, Polynomial.natDegree_C_mul_of_isUnit]
  · exact S2574P_natDegree
  · exact IsUnit.of_mul_eq_one _ (Units.inv_mul S2574_lead_unit.unit)

lemma S2574f_coeff12 : S2574f.coeff 12 = 1 := by
  have hdeg := S2574f_natDegree
  rw [← hdeg, ← Polynomial.leadingCoeff]
  exact S2574f_monic

def fbar (W : S2584PrimeDegreeOneWitness) : (S ⧸ W.P)[X] :=
  S2574f.map (Ideal.Quotient.mk W.P)

lemma fbar_natDegree (W : S2584PrimeDegreeOneWitness) : (fbar W).natDegree = 12 := by
  haveI : W.P.IsMaximal := S2586_P_isMaximal W
  haveI : Field (S ⧸ W.P) := Ideal.Quotient.field W.P
  have hle : (fbar W).natDegree ≤ 12 := by
    rw [fbar]
    calc (S2574f.map (Ideal.Quotient.mk W.P)).natDegree
        ≤ S2574f.natDegree := Polynomial.natDegree_map_le
      _ = 12 := S2574f_natDegree
  have hcoeff : (fbar W).coeff 12 = 1 := by
    rw [fbar, Polynomial.coeff_map, S2574f_coeff12]
    simp
  apply natDegree_eq_of_le_of_coeff_ne_zero hle
  rw [hcoeff]
  exact one_ne_zero

/-- The only missing arithmetic field: irreducibility of the reduced monic model. -/
def S2587FbarIrreducibleRequired (W : S2584PrimeDegreeOneWitness) : Prop :=
  Irreducible (fbar W)

/-- S-version of the localized residue data. -/
structure S2587LocalizedResidueDataS where
  p : Ideal S
  p_max : p.IsMaximal
  fbar_irreducible : Irreducible (S2574f.map (Ideal.Quotient.mk p))
  fbar_degree : (S2574f.map (Ideal.Quotient.mk p)).natDegree = 12

/-- S-version of the remaining Dedekind-to-twelve-cycle transport. -/
def S2587LocalizedDedekindToTwelveCycleS : Prop :=
  ∀ _D : S2587LocalizedResidueDataS,
    LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual.S2440TwelveCycleInputRequired

/-- Assembly: witness + fbar irreducibility gives the S-version localized residue data. -/
def S2587ResidueDataOfWitness (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W) :
    S2587LocalizedResidueDataS :=
  { p := W.P
    p_max := S2586_P_isMaximal W
    fbar_irreducible := hirr
    fbar_degree := fbar_natDegree W }

theorem S2587Target_of_witness_irreducible
    (W : S2584PrimeDegreeOneWitness) (hirr : S2587FbarIrreducibleRequired W)
    (htrans : S2587LocalizedDedekindToTwelveCycleS) :
    LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target :=
  LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target_of_twelveCycle
    (htrans (S2587ResidueDataOfWitness W hirr))

end LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
end