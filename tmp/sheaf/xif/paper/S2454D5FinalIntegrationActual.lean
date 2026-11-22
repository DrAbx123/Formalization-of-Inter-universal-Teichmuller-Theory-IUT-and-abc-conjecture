import tmp.sheaf.xif.paper.S2453BetaTransitiveActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
open LeanFormal.IUT.XiFPaper.S2446D5FinalActual
open LeanFormal.IUT.XiFPaper.S2453BetaTransitiveActual
namespace LeanFormal.IUT.XiFPaper.S2454D5FinalIntegrationActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
abbrev s2454Beta : Type := {g : ((RingOfIntegers K) ⧸ p)[X] //
  g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}
include hp hP hPover hmonic in
local instance s2454BetaFintype : Fintype (s2454Beta K f p) :=
  s2453Beta_fintype K f p
include hp hP hPover hmonic hsep hsplit in
theorem s2454PermBar_cycleType_raw :
    (permBar (f := f) p P).cycleType =
      (Finset.univ.filter (fun b : s2454Beta K f p => 2 ≤ b.1.natDegree)).val.map
        (fun b => b.1.natDegree) := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  refine cycleType_eq_fiber_sizes (permBar (f := f) p P)
    (s2425RootFactor f p P hmonic hsep) (fun b => b.1.natDegree) ?_ ?_ ?_
  · intro x
    exact s2425RootFactor_permBar f p P hmonic hsep x
  · intro b
    exact s2446Fiber_card K L f p P hmonic hsep hsplit b
  · intro b x y hx hy
    exact s2453Fibre_transitive K L f p P hmonic hsep hsplit b x y hx hy
#print axioms s2454PermBar_cycleType_raw
end LeanFormal.IUT.XiFPaper.S2454D5FinalIntegrationActual
end
