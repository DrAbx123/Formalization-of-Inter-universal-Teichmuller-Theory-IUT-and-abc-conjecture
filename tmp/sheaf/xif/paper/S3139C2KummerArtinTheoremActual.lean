import Brauer.DualityH1
import Brauer.FundamentalClass
import tmp.sheaf.xif.paper.S3139C2LocalKummerCopyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000
set_option linter.defProp false

/-!
# S3139: C2 — the Galois-Kummer compatibility becomes a theorem (Brauer pairing reuse)

The C2 Kummer copy action (`S3139C2LocalKummerCopyActual`) recorded the
Galois-Kummer identification as a data structure.  Reusing the existing Brauer
port (lakefile lib Brauer), the compatibility is NOT new data: it is the theorem
`PadicField.pairingH1_kummer` (Brauer/DualityH1.lean:110)

  pairingH1 n chi (kummer n K Omega a) = artinChar n chi a,

i.e. the local duality pairing of the Kummer class of a copy computes the Artin
character of the copy (IUT III:616-620, Fig. I.5; the Brauer-theoretic form is
Brauer/FundamentalClass.lean:24-26).

This file:
* states the pairing-level compatibility structure
  `SourceKummerArtinPairingCompatibility` and CONSTRUCTS it from
  `PadicField.pairingH1_kummer` (so the compatibility is a theorem);
* records the route refutation of the earlier hom-level shape
  `SourceKummerArtinCompatibility`: applied to n-th powers it would force the
  Artin map to kill all n-th powers (since the Kummer map kills n-th powers),
  which is false for local CFT -- a negative result, not promoted.

No sorry/axiom/True/PUnit/toy carrier.  **Component, not paper object.**
-/

namespace LeanFormal.IUT.XiFPaper.S3139C2KummerArtinTheoremActual

open LeanFormal.IUT.XiFPaper.S3139C2LocalKummerCopyActual
open KummerTheory

universe uK uΩ

/-! ## 1. The pairing-level compatibility (the paper's actual form) -/

/-- The paper-faithful Galois-Kummer compatibility at the pairing level: the
local duality pairing of the Kummer class of a copy computes its Artin
character (Brauer/DualityH1.lean:110; refs III:616-620, Fig. I.5). -/
structure SourceKummerArtinPairingCompatibility
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type uK) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
    (n : ℕ) [NeZero n] [KummerTheory.HasKummerRoots n K Ω]
    [Algebra.IsIntegral K Ω] where
  /-- the local duality pairing of the Kummer class equals the Artin character -/
  pairing_eq : ∀ (χ : Brauer.LocChar K Ω n) (a : Kˣ),
    PadicField.pairingH1 (p := p) n χ (sourceLocalKummerClass n K Ω a) =
      PadicField.artinChar (p := p) n χ a

/-- The Galois-Kummer compatibility IS a theorem: constructed from the Brauer
port's `PadicField.pairingH1_kummer`.  No new missing data. -/
noncomputable def sourceKummerArtinPairingCompatibility
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type uK) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
    (n : ℕ) [NeZero n] [KummerTheory.HasKummerRoots n K Ω]
    [Algebra.IsIntegral K Ω] :
    SourceKummerArtinPairingCompatibility p K Ω n where
  pairing_eq := fun χ a => by
    show PadicField.pairingH1 (p := p) n χ ((KummerTheory.kummer n K Ω) a) =
      PadicField.artinChar (p := p) n χ a
    exact PadicField.pairingH1_kummer (p := p) n χ a

/-- The pairing-level compatibility is inhabited (fully proved, not assumed). -/
theorem sourceKummerArtinPairingCompatibility_nonempty
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type uK) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
    (n : ℕ) [NeZero n] [KummerTheory.HasKummerRoots n K Ω]
    [Algebra.IsIntegral K Ω] :
    Nonempty (SourceKummerArtinPairingCompatibility p K Ω n) :=
  ⟨sourceKummerArtinPairingCompatibility p K Ω n⟩

/-- The compatibility statement, re-exported for consumers: the local duality
pairing of the Kummer class of the copy is the Artin character. -/
theorem sourceKummerArtinPairing_eq
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type uK) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
    (n : ℕ) [NeZero n] [KummerTheory.HasKummerRoots n K Ω]
    [Algebra.IsIntegral K Ω]
    (χ : Brauer.LocChar K Ω n) (a : Kˣ) :
    PadicField.pairingH1 (p := p) n χ (sourceLocalKummerClass n K Ω a) =
      PadicField.artinChar (p := p) n χ a :=
  PadicField.pairingH1_kummer (p := p) n χ a

/-! ## 2. Negative result: the hom-level shape is refuted -/

/-- Route refutation of the earlier hom-level data shape: a monoid hom from the
local Kummer H1 to Gal(maxAbelian) sending the Kummer class of a to artin a
would force the Artin map to kill every n-th power, because the Kummer map kills
n-th powers.  This is false for local CFT (the Artin map of a uniformizer has
infinite order), so the hom-level shape is a modeling error; the paper-faithful
form is the pairing-level theorem above.  Recorded as a negative result, not
promoted. -/
theorem kummerHomLevel_forces_artin_pow_trivial
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type uK) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
    (n : ℕ) [NeZero n] [KummerTheory.HasKummerRoots n K Ω]
    [Algebra.IsIntegral K Ω]
    (C : SourceKummerArtinCompatibility p K Ω n) (a : Kˣ) :
    sourceLocalArtinMap p K Ω (a ^ n) = 1 := by
  have hk : sourceLocalKummerClass n K Ω (a ^ n) = 1 := by
    have hmem : KummerTheory.kummer n K Ω (a ^ n) = 1 := by
      have hker : a ^ n ∈ (KummerTheory.kummer n K Ω).ker := by
        rw [KummerTheory.ker_kummer]
        exact ⟨a, rfl⟩
      exact MonoidHom.mem_ker.mp hker
    show KummerTheory.kummer n K Ω (a ^ n) = 1
    exact hmem
  have h := C.comparison_kummer (a ^ n)
  rw [hk, map_one] at h
  exact h.symm

end LeanFormal.IUT.XiFPaper.S3139C2KummerArtinTheoremActual

end
