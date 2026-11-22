import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerContinuity
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerQuotient
import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment
import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient

/-!
# Mzk1KummerThetaInterfaceActual — iuti-ii Kummer/Theta interface asset layer

STEP 0 prior-art: tree Kummer layer AbsoluteKummerInjection (absoluteKummerMap, kernel =
n-th powers), AbsoluteKummerContinuity (locally constant/continuous in the Galois variable),
AbsoluteKummerQuotient (K^x/(K^x)^n injection), SourceThetaPilotIQContainment (theta-pilot
orbit containment), and IUTII/Theta/EtaleThetaQuotient (theta quotient / power kernels /
mod-l projections) -> REUSE; no new mathematics and no high-level wiring.

WHAT THIS FILE DOES (asset-first interface):
* re-exports the Kummer facts as theta-layer named declarations (class map, continuity,
  quotient injectivity) via aliases of the exact tree declarations;
* packages the etale theta quotient data in a typed ThetaQuotientInterface
  (thetaToElliptic + surjectivity, mod-l theta projections + surjectivity);
* packages the absolute Kummer layer in a typed KummerLayerInterface (class map +
  quotient injection; continuity re-exported separately);
* re-exports the theta-pilot IQ containment/generator facts;
* records the rows connecting this interface to the EtTh rows, keeping the deep EtTh
  rigidity inputs NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual

open LeanFormal.IUT

/-! ## 1. Re-exported Kummer facts (tree proofs) -/

/-- The absolute Kummer class map (tree: AbsoluteKummerInjection.absoluteKummerMap). -/
noncomputable def kummerClass :=
  @AbsoluteKummerInjection.absoluteKummerMap

/-- Continuity of the absolute Kummer class in the Galois variable (tree proof). -/
def kummerClass_continuous :=
  @AbsoluteKummerContinuity.continuous_absoluteKummerMap

/-- The quotient Kummer map is injective (tree proof). -/
def kummerQuotient_injective :=
  @AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective

/-! ## 2. Typed theta quotient interface (tree EtaleThetaQuotient) -/

/-- The etale theta quotient data: the theta-to-elliptic map and the mod-l theta
projections, together with their tree-proved surjectivity. -/
structure ThetaQuotientInterface (G : Type*) [Group G] where
  thetaToElliptic : ThetaQuotient G →* EllipticAbelianization G
  thetaToElliptic_surjective : Function.Surjective thetaToElliptic
  modLThetaProjection : ∀ l : Nat, G →* ModLThetaQuotient G l
  modLThetaProjection_surjective : ∀ l : Nat, Function.Surjective (modLThetaProjection l)

/-- The theta quotient interface is inhabited by the tree data. -/
def thetaQuotientInterface (G : Type*) [Group G] : ThetaQuotientInterface G where
  thetaToElliptic := thetaToElliptic G
  thetaToElliptic_surjective := thetaToElliptic_surjective G
  modLThetaProjection := fun l => modLThetaProjection G l
  modLThetaProjection_surjective := fun l => modLThetaProjection_surjective G l

/-- The theta commutator kernel lies in the derived subgroup (tree proof). -/
def thetaCommutatorKernel_le_derived :=
  @thetaCommutatorKernel_le_derivedSubgroup

/-! ## 3. Typed absolute Kummer layer interface -/

/-- The absolute Kummer layer at (K, n, hμ): the class map and the quotient injection. -/
structure KummerLayerInterface (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) where
  kummerMap : Kˣ →* ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
    rootsOfUnity n (AlgebraicClosure K))
  quotient_injective : Function.Injective
    (AbsoluteKummerQuotient.absoluteKummerMapQuotient hμ)

/-- The absolute Kummer layer interface is inhabited by the tree data. -/
def kummerLayerInterface (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    KummerLayerInterface K n hμ where
  kummerMap := AbsoluteKummerInjection.absoluteKummerMap hμ
  quotient_injective := AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective hμ

/-! ## 4. Theta-pilot IQ containment (tree proofs, re-exported) -/

/-- Theta-pilot orbit containment (tree proof). -/
def thetaPilot_orbit_containment :=
  @possibleImage_subset_of_generator_mem

/-- The source log-shell tensor generator lies in the source theta-pilot IQ packet
(tree proof). -/
def thetaPilot_generator_mem :=
  @sourceLogShellTensorGenerator_mem_sourceThetaPilotIQPacket

/-! ## 5. Interface rows -/

/-- Kummer/Theta interface rows: (asset, tree source/consumer, status). -/
def kummerThetaInterfaceRows : List (String × String × String) :=
  [ ("absolute Kummer class + kernel = n-th powers", "AbsoluteKummerInjection.absoluteKummerMap/absoluteKummerMap_eq_one_iff", "TREE PROOF (olean ✓; A428 build pin)"),
    ("continuity/locally constant in Galois variable", "AbsoluteKummerContinuity.isLocallyConstant_absoluteKummerMap/continuous_absoluteKummerMap", "TREE PROOF + re-export (kummerClass_continuous)"),
    ("K^x/(K^x)^n injection", "AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective", "TREE PROOF + re-export (kummerQuotient_injective)"),
    ("etale theta quotient/power kernels/mod-l projections", "IUTII/Theta/EtaleThetaQuotient", "TREE ASSET + typed ThetaQuotientInterface"),
    ("theta-pilot orbit containment / generator membership", "SourceThetaPilotIQContainment.possibleImage_subset_of_generator_mem / sourceLogShellTensorGenerator_mem_sourceThetaPilotIQPacket", "TREE PROOF + re-export"),
    ("EtTh §1/§4 deep rigidity (theta action/etale theta class/bi-Kummer)", "EtTh02/EtTh03 named deep inputs", "NAMED (not claimed here)") ]

/-- The Kummer/Theta interface row record has six rows. -/
theorem kummerThetaInterfaceRows_length : kummerThetaInterfaceRows.length = 6 := rfl

#check kummerClass
#check kummerClass_continuous
#check kummerQuotient_injective
#check ThetaQuotientInterface
#check thetaQuotientInterface
#check KummerLayerInterface
#check kummerLayerInterface
#check thetaPilot_orbit_containment
#check thetaPilot_generator_mem
#check kummerThetaInterfaceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual
end
