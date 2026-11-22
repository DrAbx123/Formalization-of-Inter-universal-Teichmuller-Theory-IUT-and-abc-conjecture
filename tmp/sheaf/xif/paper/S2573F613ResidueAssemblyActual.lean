import tmp.sheaf.xif.paper.S2572F613IrreducibleActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual

noncomputable section
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2573F613ResidueAssemblyActual

/-- Residue data whose only new certificate is the identification of its
reduction with F613.  All other fields are the actual S2470 residue data. -/
structure S2573F613ResidueData where
  f : (RingOfIntegers S1720Field)[X]
  p : Ideal (RingOfIntegers S1720Field)
  P : Ideal (RingOfIntegers S2057FiveDivisionField)
  p_max : p.IsMaximal
  P_prime : P.IsPrime
  P_lies : P.LiesOver p
  f_monic : f.Monic
  f_sep : (fbar f p).Separable
  f_splits : (f.map
    (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits
  f_psi5 : ∃ c : S1720Field, c ≠ 0 ∧
    f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F
  residueEquiv : (RingOfIntegers S1720Field ⧸ p) ≃+* ZMod 613
  fbar_map : (fbar f p).map residueEquiv.toRingHom = F613
  fbar_degree : (fbar f p).natDegree = 12
  fbar_card : Fintype.card ((fbar f p).rootSet
    ((RingOfIntegers S2057FiveDivisionField) ⧸ P)) = 12

/-- F613 irreducibility supplies the S2470 irreducibility field. -/
noncomputable def S2573F613ResidueData.toActual
    (R : S2573F613ResidueData) : S2470ActualResidueData where
  f := R.f
  p := R.p
  P := R.P
  p_max := R.p_max
  P_prime := R.P_prime
  P_lies := R.P_lies
  f_monic := R.f_monic
  f_sep := R.f_sep
  f_splits := R.f_splits
  f_psi5 := R.f_psi5
  fbar_irreducible := by
    have hI : Irreducible
        ((Polynomial.mapEquiv R.residueEquiv) (fbar R.f R.p)) := by
      rw [show (Polynomial.mapEquiv R.residueEquiv) (fbar R.f R.p) = F613
        from R.fbar_map]
      exact F613_irreducible
    exact (MulEquiv.irreducible_iff
      (f := Polynomial.mapEquiv R.residueEquiv)).mp hI
  fbar_degree := R.fbar_degree
  fbar_card := R.fbar_card

/-- The 12-cycle follows from the residue data and F613 irreducibility. -/
theorem S2573_rootTwelveCycle (R : S2573F613ResidueData) :
    ∃ σ : Gal(S2057FiveDivisionField/S1720Field),
      rootCycleType S1720Field S2057FiveDivisionField R.f R.f_splits σ =
        ({12} : Multiset Nat) :=
  R.toActual.rootTwelveCycle

#check S2573F613ResidueData
#check S2573F613ResidueData.toActual
#check S2573_rootTwelveCycle

end LeanFormal.IUT.XiFPaper.S2573F613ResidueAssemblyActual
end
