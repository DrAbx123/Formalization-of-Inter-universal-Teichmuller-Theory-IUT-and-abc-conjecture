import tmp.sheaf.xif.paper.S2536LocalizedPowersActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2535LocalizedIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

namespace LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizedActualAdapted

abbrev S2537A : Type := NumberField.RingOfIntegers S1720Field
abbrev S2537C : Type := NumberField.RingOfIntegers S2057FiveDivisionField
abbrev S2537K : Type := S1720Field
abbrev S2537L : Type := S2057FiveDivisionField

instance S2537IntegralClosure : IsIntegralClosure S2537C S2537A S2537L :=
  IsIntegralClosure.tower_top (R := ℤ) (A := S2537A) (B := S2537L) (C := S2537C)

theorem S2537_h10 : (10 : S2537A) ≠ 0 := by
  intro h
  have h' : algebraMap S2537A S2537K (10 : S2537A) = 0 := by rw [h, map_zero]
  norm_num at h'

theorem S2537_h10_mem : (10 : S2537A) ∈ nonZeroDivisors S2537A :=
  mem_nonZeroDivisors_of_ne_zero S2537_h10

theorem S2537_isIntegralClosure (R S : Type*)
    [CommRing R] [CommRing S] [Algebra S2537A R] [Algebra S2537C S]
    [Algebra S2537A S2537K] [Algebra S2537A S2537L]
    [Algebra S2537A S2537C] [Algebra S2537C S2537L]
    [FaithfulSMul S2537A S2537C]
    [IsLocalization (Submonoid.powers (10 : S2537A)) R]
    [IsLocalization (Algebra.algebraMapSubmonoid S2537C (Submonoid.powers (10 : S2537A))) S]
    [Algebra R S] [Algebra S2537A S]
    [Algebra R S2537L] [Algebra S S2537L] :
    IsIntegralClosure S R S2537L := by
  letI : SMul S2537A S2537C := Algebra.toSMul
  letI : SMul S2537C S2537L := Algebra.toSMul
  letI : SMul S2537A S2537L := Algebra.toSMul
  letI : SMul S2537A R := Algebra.toSMul
  letI : SMul R S := Algebra.toSMul
  letI : SMul S2537A S := Algebra.toSMul
  letI : SMul R S2537L := Algebra.toSMul
  letI : SMul S S2537L := Algebra.toSMul
  have   have hACL : IsScalarTower S2537A S2537C S2537L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x; rfl : hACL := inferInstance
  have   have hARS : IsScalarTower S2537A R S := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x; rfl : hARS := inferInstance
  have   have hACS : IsScalarTower S2537A S2537C S := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x; rfl : hACS := inferInstance
  have   have hARL : IsScalarTower S2537A R S2537L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x; rfl : hARL := inferInstance
  have   have hCSL : IsScalarTower S2537C S S2537L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x; rfl : hCSL := inferInstance
  have   have hRSL : IsScalarTower R S S2537L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x; rfl : hRSL := inferInstance
  haveI := hACL
  haveI := hARS
  haveI := hACS
  haveI := hARL
  haveI := hCSL
  haveI := hRSL
  exact isIntegralClosure_localization_powers
    (A := S2537A) (C := S2537C) (K := S2537K) (L := S2537L)
    (R := R) (S := S) (a := (10 : S2537A)) S2537_h10_mem

#check S2537_isIntegralClosure

end LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizedActualAdapted
end