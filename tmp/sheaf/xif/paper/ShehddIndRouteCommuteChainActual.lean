import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithmReduction

/-!
# ShehddIndRouteCommuteChainActual — multiradial route construction functoriality chain

Reuses the compiled uncovered tree asset Theorem311/Output/MultiradialAlgorithmReduction
(an ACTUAL-TARGETS iut-skeleton:Thm311 prerequisite) as genuine chain theorems: the route
construction is functorial under (Ind1)/(Ind2) with invariant log-volume, upper-semi under
(Ind3), and descends unchanged through horizontal routes.

No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddIndRouteCommuteChainActual

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialAlgorithmReduction

universe u v

/-- **PROVED chain:** the route construction commutes with both (Ind1) and (Ind2) actions,
and its procession-normalized log-volume is invariant under both. -/
theorem route_ind12_functorial_chain {Label : Type u} {Choice : Type v}
    [AddCommGroup Label] (core : Core Label Choice) (profile : Profile core)
    (route : List (RouteStep Label)) (g : Label) (c : Choice) :
    applyRoute core route (core.ind1 g c) =
        core.ind1 g (applyRoute core route c) ∧
      applyRoute core route (core.ind2 g c) =
        core.ind2 g (applyRoute core route c) ∧
      profile.logVolume (applyRoute core route (core.ind1 g c)) =
        profile.logVolume (applyRoute core route c) ∧
      profile.logVolume (applyRoute core route (core.ind2 g c)) =
        profile.logVolume (applyRoute core route c) :=
  ⟨applyRoute_ind1_commute core route g c,
    applyRoute_ind2_commute core route g c,
    applyRoute_ind1_commute_logVolume core profile route g c,
    applyRoute_ind2_commute_logVolume core profile route g c⟩

/-- **PROVED chain:** the route construction commutes with the (Ind3) log-link action and
the output log-volume is upper-semi compatible with it. -/
theorem route_ind3_upper_chain {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : Core Label Choice) (profile : Profile core)
    (route : List (RouteStep Label)) (n : Nat) (c : Choice) :
    applyRoute core route (core.ind3 n c) =
        core.ind3 n (applyRoute core route c) ∧
      profile.logVolume (applyRoute core route c) ≤
        profile.logVolume (applyRoute core route (core.ind3 n c)) :=
  ⟨applyRoute_ind3_commute core route n c,
    applyRoute_ind3_commute_logVolume_le core profile route n c⟩

/-- **PROVED chain:** a horizontal route descends to the joint indeterminacy quotient
unchanged (quotient form of the (Ind1)/(Ind2) invariance). -/
theorem route_horizontal_quotient_chain {Label : Type u} {Choice : Type v}
    [AddGroup Label] (core : Core Label Choice) (route : List (RouteStep Label))
    (hroute : ∀ step ∈ route, horizontal step) (c : Choice) :
    Core.generatedQuotientMap core (applyRoute core route c) =
      Core.generatedQuotientMap core c :=
  applyRoute_horizontal_quotient_eq core route hroute c

end LeanFormal.IUT.XiFPaper.ShehddIndRouteCommuteChainActual
end
