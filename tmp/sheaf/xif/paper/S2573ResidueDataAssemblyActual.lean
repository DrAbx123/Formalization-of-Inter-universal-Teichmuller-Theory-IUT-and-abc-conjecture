import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2572F613IrreducibleActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2573ResidueDataAssemblyActual

open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual

/-!
# S2573: assembly of S2470ActualResidueData

Status table (actual / conditional):

* f monic integral model of a nonzero F'-multiple of psi5: MISSING.
* p maximal over 613 with residue degree one: MISSING (candidate from H613_splits).
* P above p: MISSING.
* f_sep / f_splits: conditional on the model and splitting field.
* f_psi5: definitional from the chosen model.
* fbar irreducible degree 12: actual in principle from F613_irreducible
  once an isomorphism (O_F'/p) = ZMod 613 and fbar = F613 are supplied.
* fbar_card = 12: MISSING (needs the residue root-set identification).
-/

structure S2573ResidueDataObligations where
  f : (NumberField.RingOfIntegers S1720Field)[X]
  p : Ideal (NumberField.RingOfIntegers S1720Field)
  P : Ideal (NumberField.RingOfIntegers S2057FiveDivisionField)
  p_max : p.IsMaximal
  p_over_613 : p.LiesOver (Ideal.span ({613} : Set ℤ))
  p_inertia_one : p.inertiaDeg ℤ = 1
  P_prime : P.IsPrime
  P_lies : P.LiesOver p
  f_monic : f.Monic
  f_sep : (fbar f p).Separable
  f_splits : (f.map
    (algebraMap (NumberField.RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits
  f_psi5 : ∃ c : S1720Field, c ≠ 0 ∧
    f.map (algebraMap (NumberField.RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F
  fbar_irreducible : Irreducible (fbar f p)
  fbar_degree : (fbar f p).natDegree = 12
  fbar_card : Fintype.card ((fbar f p).rootSet
    ((NumberField.RingOfIntegers S2057FiveDivisionField) ⧸ P)) = 12

def S2573ResidueDataObligations.toResidueData
    (O : S2573ResidueDataObligations) : S2470ActualResidueData :=
  { f := O.f
    p := O.p
    P := O.P
    p_max := O.p_max
    P_prime := O.P_prime
    P_lies := O.P_lies
    f_monic := O.f_monic
    f_sep := O.f_sep
    f_splits := O.f_splits
    f_psi5 := O.f_psi5
    fbar_irreducible := O.fbar_irreducible
    fbar_degree := O.fbar_degree
    fbar_card := O.fbar_card }

def S2573MinimalRemaining : Prop := Nonempty S2573ResidueDataObligations

theorem S2573_twelveCycle (h : S2573MinimalRemaining) :
    ∃ D : S2470ActualResidueData,
      ∃ σ : Gal(S2057FiveDivisionField/S1720Field),
        rootCycleType S1720Field S2057FiveDivisionField D.f D.f_splits σ =
          ({12} : Multiset ℕ) := by
  obtain ⟨O⟩ := h
  let D := O.toResidueData
  exact ⟨D, D.rootTwelveCycle⟩

theorem S2573Target_of_minimal_and_transport
    (h : S2573MinimalRemaining) (htrans : S2470RootToRangeTransport) :
    S2470Target := by
  obtain ⟨O⟩ := h
  exact S2470Target_of_residueData_and_transport O.toResidueData htrans

end LeanFormal.IUT.XiFPaper.S2573ResidueDataAssemblyActual
end