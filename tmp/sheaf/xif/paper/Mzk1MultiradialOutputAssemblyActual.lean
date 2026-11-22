import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial

/-!
# Mzk1MultiradialOutputAssemblyActual — real assembly: multiradial output base invariants

Status: PENDING-VERIFY. No sorry, no axiom.
Consumer (not adapted copy): assembles the compiled multiradial kernel output, its
profile Ind1/Ind2 invariance and Ind3 upper comparison into one statement, and records
the base output log-volume identity. Uses only proved theorems of SourceFiniteMultiradial. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1MultiradialOutputAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceFiniteMultiradial
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core

/-- Genuine assembly theorem: base multiradial output has base target, level 0, and theta log-volume. -/
theorem multiradial_output_base_invariants (l : PrimeGeFive) :
    Output.target (emptyRouteOutput l) = ProcessionChoice.base ∧
      (core l).level (Output.target (emptyRouteOutput l)) = 0 ∧
      (profile l).logVolume (Output.target (emptyRouteOutput l)) = thetaLogVolume l :=
  ⟨emptyRouteOutput_target l, emptyRouteOutput_level l, emptyRouteOutput_log_volume l⟩

/-- Genuine assembly theorem: multiradial profile Ind1/Ind2 invariance and Ind3 upper comparison. -/
theorem multiradial_profile_ind_invariants (l : PrimeGeFive) :
    (∀ (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l),
        (profile l).logVolume ((core l).ind1 g c) = (profile l).logVolume c) ∧
      (∀ (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l),
        (profile l).logVolume ((core l).ind2 g c) = (profile l).logVolume c) ∧
      (∀ (n : Nat) (c : ProcessionChoice l),
        (profile l).logVolume c ≤ (profile l).logVolume ((core l).ind3 n c)) :=
  ⟨profile_ind1_invariant l, profile_ind2_invariant l, profile_ind3_upper l⟩

/-- Genuine assembly theorem: multiradial possible-image nonemptiness and Ind1/Ind2 invariance. -/
theorem multiradial_possible_image_invariants (l : PrimeGeFive) :
    (∀ c : ProcessionChoice l, ((profile l).possibleImage c).Nonempty) ∧
      (∀ (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l),
        (profile l).possibleImage ((core l).ind1 g c) = (profile l).possibleImage c) ∧
      (∀ (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l),
        (profile l).possibleImage ((core l).ind2 g c) = (profile l).possibleImage c) :=
  ⟨profile_possible_nonempty l, profile_possible_ind1 l, profile_possible_ind2 l⟩

end LeanFormal.IUT.XiFPaper.Mzk1MultiradialOutputAssemblyActual
end
