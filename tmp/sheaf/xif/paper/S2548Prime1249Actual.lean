import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S2531Mod1249SplittingActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2548Prime1249Actual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2531Mod1249SplittingActual
abbrev A : Type := RingOfIntegers S1720Field
lemma S1720H_map1249 :
    S1720H.map (algebraMap ℚ (ZMod 1249)) =
      LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ.map
        (Int.castRingHom (ZMod 1249)) := by
  rw [← LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ_map_rat]
  rw [Polynomial.map_map]
  congr 1
  ext n
  simp
lemma S1720H_splits1249 :
    (S1720H.map (algebraMap ℚ (ZMod 1249))).Splits := by
  rw [S1720H_map1249]
  exact S2531Mod1249ResidueDegreeOne_actual
noncomputable def alg1249 : S1720Field →ₐ[ℚ] ZMod 1249 :=
  Polynomial.SplittingField.lift (f := S1720H) (L := ZMod 1249) S1720H_splits1249
noncomputable def phi1249 : A →+* ZMod 1249 :=
  (alg1249 : S1720Field →+* ZMod 1249).comp (algebraMap A S1720Field)
noncomputable def p1249 : Ideal A := RingHom.ker phi1249
instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩
lemma phi1249_int (n : ℤ) : phi1249 (algebraMap ℤ A n) = (n : ZMod 1249) := by
  have h1 : (algebraMap A S1720Field) (algebraMap ℤ A n) = algebraMap ℤ S1720Field n := by
    rw [IsScalarTower.algebraMap_apply ℤ A S1720Field]
  rw [phi1249, RingHom.comp_apply, h1]
  change (alg1249 : S1720Field →+* ZMod 1249) (algebraMap ℚ S1720Field (n : ℚ)) = (n : ZMod 1249)
  rw [AlgHom.commutes]
  norm_num
lemma p1249_ne_bot : p1249 ≠ ⊥ := by
  intro h
  have hmem : (1249 : A) ∈ p1249 := by
    rw [p1249, RingHom.mem_ker]
    have h1249 : (1249 : A) = algebraMap ℤ A (1249 : ℤ) := by norm_num
    rw [h1249, phi1249_int]
    norm_num
  rw [h] at hmem
  exact (Ideal.mem_bot.mp hmem) (by norm_num)
lemma p1249_isMaximal : p1249.IsMaximal := by
  haveI : IsDedekindDomain A := inferInstance
  exact Ideal.IsPrime.isMaximal (RingHom.ker_isPrime phi1249) p1249_ne_bot
#print axioms p1249_isMaximal
end LeanFormal.IUT.XiFPaper.S2548Prime1249Actual
end
