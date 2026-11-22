import tmp.sheaf.xif.paper.S2643RootTransportFixActual
import tmp.sheaf.xif.paper.S2642RootToRangeTransport
import tmp.sheaf.xif.paper.S2652RootBijectionActual
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2643RootTransportFixActual
open LeanFormal.IUT.XiFPaper.S2642RootToRangeTransport
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

namespace LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual

theorem S2653rootSet_eq_of_eq_smul
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    {p q : K[X]} {c : K} (hc : c ≠ 0) (hq : q = C c * p) :
    q.rootSet A = p.rootSet A := by
  classical
  have hcA : algebraMap K A c ≠ 0 := by
    intro h
    have h1 : (1 : A) = 0 := by
      calc
        (1 : A) = algebraMap K A (c * c⁻¹) := by
          rw [mul_inv_cancel₀ hc, map_one]
        _ = algebraMap K A c * algebraMap K A c⁻¹ := by rw [map_mul]
        _ = 0 := by rw [h, zero_mul]
    exact one_ne_zero h1
  ext x
  rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet']
  constructor
  · rintro ⟨hqne, hx⟩
    refine ⟨?_, ?_⟩
    · intro hp0
      apply hqne
      rw [hq, Polynomial.map_mul, Polynomial.map_C, hp0]
      simp
    · rw [hq, Polynomial.aeval_mul, Polynomial.aeval_C] at hx
      exact (mul_eq_zero.mp hx).resolve_left hcA
  · rintro ⟨hpne, hx⟩
    refine ⟨?_, ?_⟩
    · rw [hq, Polynomial.map_mul, Polynomial.map_C]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hcA) hpne
    · rw [hq, Polynomial.aeval_mul, Polynomial.aeval_C, hx]
      simp

noncomputable def S2653rootSetEquiv
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    {p q : K[X]} {c : K} (hc : c ≠ 0) (hq : q = C c * p) :
    q.rootSet A ≃ p.rootSet A :=
  Equiv.subtypeEquivRight
    (fun x => (Set.ext_iff.mp
      (S2653rootSet_eq_of_eq_smul (K := K) (A := A) hc hq)) x)

theorem S2653rootPerm_apply_val
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (σ : Gal(L/K))
    (x : (f.map (algebraMap (RingOfIntegers K) K)).rootSet L) :
    (rootPerm K L f hsplit σ x).1 = σ x.1 := by
  simp only [rootPerm, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

theorem S2653permCongr_rootPerm_eq_divisionRootEquiv
    (f : (RingOfIntegers S1720Field)[X])
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
      C c * S2057Psi5F) :
    (S2653rootSetEquiv (K := S1720Field) (A := S2057FiveDivisionField)
      hc hq).permCongr
        (rootPerm S1720Field S2057FiveDivisionField f hsplit σ) =
      S2132DivisionRootEquiv σ := by
  ext x
  rw [Equiv.permCongr_apply]
  change
    (rootPerm S1720Field S2057FiveDivisionField f hsplit σ
      ((S2653rootSetEquiv (K := S1720Field) (A := S2057FiveDivisionField)
        hc hq).symm x)).1
      = (S2132DivisionRootEquiv σ x).1
  rw [S2653rootPerm_apply_val]
  rfl


theorem S2653rootPerm_cycleType_rootCycleType
    (f : (RingOfIntegers S1720Field)[X])
    (p : Ideal (RingOfIntegers S1720Field)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers S2057FiveDivisionField)) [hP : P.IsPrime]
    [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field)
        S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    (H : @IsArithFrobAt (RingOfIntegers S1720Field)
      (RingOfIntegers S2057FiveDivisionField) _ _ _
      Gal(S2057FiveDivisionField/S1720Field) _
      (instMulSemiringActionAlgEquivRingOfIntegers_tmp S1720Field
        S2057FiveDivisionField)
      (instSMulCommClassAlgEquivRingOfIntegers_tmp S1720Field
        S2057FiveDivisionField) σ P) :
    (rootPerm S1720Field S2057FiveDivisionField f hsplit σ).cycleType =
      rootCycleType S1720Field S2057FiveDivisionField f hsplit σ := by
  classical
  have h := s2440RootPermBar_cycleType_rootCycleType
    (K := S1720Field) (L := S2057FiveDivisionField)
    (f := f) (p := p) (P := P) hmonic hsep hsplit σ H
  rw [s2440RootPermBar_eq_permCongr_rootPerm
    (K := S1720Field) (L := S2057FiveDivisionField)
    (f := f) (p := p) (P := P) hmonic hsep hsplit σ H] at h
  letI : DecidableEq
      (f.rootSet (RingOfIntegers S2057FiveDivisionField)) :=
    Classical.decEq _
  rw [S2132cycleType_permCongr] at h
  exact h

theorem S2653cycleType_divisionRootEquiv_eq_rootCycleType
    (f : (RingOfIntegers S1720Field)[X])
    (p : Ideal (RingOfIntegers S1720Field)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers S2057FiveDivisionField)) [hP : P.IsPrime]
    [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
      C c * S2057Psi5F)
    (H : @IsArithFrobAt (RingOfIntegers S1720Field)
      (RingOfIntegers S2057FiveDivisionField) _ _ _
      Gal(S2057FiveDivisionField/S1720Field) _
      (instMulSemiringActionAlgEquivRingOfIntegers_tmp S1720Field
        S2057FiveDivisionField)
      (instSMulCommClassAlgEquivRingOfIntegers_tmp S1720Field
        S2057FiveDivisionField) σ P) :
    Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) =
      rootCycleType S1720Field S2057FiveDivisionField f hsplit σ := by
  rw [← S2653permCongr_rootPerm_eq_divisionRootEquiv f hsplit σ hc hq]
  rw [S2132cycleType_permCongr]
  exact S2653rootPerm_cycleType_rootCycleType f p P hmonic hsep hsplit σ H

theorem S2653S2480RootPerm_eq_S2642RootPerm
    (σ : LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual.S1725AbsoluteGalois) :
    S2480RootPerm σ = S2642RootPerm σ := by
  ext x
  rfl

theorem S2653RangeTransport
    (f : (RingOfIntegers S1720Field)[X])
    (p : Ideal (RingOfIntegers S1720Field)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers S2057FiveDivisionField)) [hP : P.IsPrime]
    [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
      C c * S2057Psi5F)
    (H : @IsArithFrobAt (RingOfIntegers S1720Field)
      (RingOfIntegers S2057FiveDivisionField) _ _ _
      Gal(S2057FiveDivisionField/S1720Field) _
      (instMulSemiringActionAlgEquivRingOfIntegers_tmp S1720Field
        S2057FiveDivisionField)
      (instSMulCommClassAlgEquivRingOfIntegers_tmp S1720Field
        S2057FiveDivisionField) σ P)
    (hcyc : rootCycleType S1720Field S2057FiveDivisionField f hsplit σ =
      ({10, 2} : Multiset ℕ)) :
    S2203RangeCycleTypeRequired S1982Basis := by
  classical
  obtain ⟨σ', hσ'⟩ := S2502cycleType_transport σ
  refine S2642RootMapToRangeTransport σ' ?_
  rw [← S2653S2480RootPerm_eq_S2642RootPerm σ', hσ',
    S2653cycleType_divisionRootEquiv_eq_rootCycleType
      f p P hmonic hsep hsplit σ hc hq H, hcyc]

#check S2653RangeTransport
#print axioms S2653RangeTransport

end LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual
end
