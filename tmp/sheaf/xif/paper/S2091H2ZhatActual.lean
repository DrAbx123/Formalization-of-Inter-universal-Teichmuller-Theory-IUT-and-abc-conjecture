/-
# S2091: the actual H²(G_v, μ̂^Z) = Ẑ computation, ported, and the S2036 (M3) normalization

Layer: **O** (original Theta-link / q-pilot).  Consumers: S2036
(tmp/sheaf/xif/paper/S2036ActualPsiCnsM234Actual.lean, the (M3) layer
PsiCnsH2Normalization) and, through it, S2046's (M4) normalization
(tmp/sheaf/xif/paper/S2046PsiCnsActionActual.lean).

## What is proved here

1. The external formalization tmp/local-cft-port/local-class-field-theory-main
   proves the local class field theory computation behind (M3):

     PadicField.h2ZHatOneEquiv : H2ZHatOne K Ω ≃* Multiplicative ZHat

   where H2ZHatOne K Ω ≤ ∏_{n : ℕ+} H²(Gal(Ω/K), μ_n) is the inverse limit of
   the finite level cohomologies along the power maps ζ ↦ ζ^(m/n) (file
   LocalClassFieldTheory/Brauer/H2ZHat.lean).  The input to that theorem is the
   cyclotomic rigidity PadicField.h2MuEquiv : H²(Gal(Ω/K), μ_n) ≃* ℤ/n, which
   is proved from PadicField.invEquiv : Br(K) ≃* ℚ/ℤ (the invariant map, via
   the Kummer sequence in degree two and the class field axiom), not
   postulated.

   This file transports that theorem to the *actual* local field of the
   project: K = ℚ_[p], Ω = AlgebraicClosure ℚ_[p], whose absolute Galois group
   AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p] is definitionally
   S2000's Gv p, and whose Ẑ is identified with S2036's Zhat.  The result is
   h2ZHatOneEquiv_of_port : Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
   Multiplicative Zhat.

2. **The exact first missing gap** is isolated as the proposition
   PsiCnsH2LimitComparison p: an isomorphism between S2036's actual continuous
   cohomology carrier PsiCnsH2 p = ContinuousH2 (PsiCnsCoefficientAction p) and
   the port's inverse limit H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]).
   PsiCnsH2Normalization_iff_limitComparison proves that this comparison is
   *exactly* equivalent to (M3); no weakening and no new hypothesis is hidden
   in it.

3. The conditional reduction (M3) is proved from the comparison
   (PsiCnsH2Normalization_of_limitComparison), and the layered (M2)/(M3)/(M4)
   statement Cor110bLayersMissing is assembled from (M2), the comparison and
   (M4).

## Why the comparison is not formalized here (the honest remainder)

The two sides are cohomology groups of the *same* group but they are built
from different cochain models and different coefficient modules:

* S2036: coefficients PsiCnsCyclotome p = Hom(ℚ/ℤ, (O^tri)ˣ), a compact
  (profinite) coefficient module, and cochains = *all continuous* functions
  G × G → coefficient;
* port: coefficients μ_n (finite, discrete), cochains = *locally constant*
  functions, and the degree-two group is formed level by level and then
  lim_n.

Closing the gap therefore needs the three comparison steps
Hom(ℚ/ℤ, μ) ≅ lim_n μ_n (topological G_v-modules), the identification of
continuous 2-cocycles into the limit with compatible families of level
cocycles, and the lim¹-vanishing lim¹_n H¹(G_v, μ_n) = 0 (the H¹ are finite).
None of the three is formalized either in the project or in the external
repository; they are the precise mathematical content of the group-theoretic
H²-normalization of [AbsTopIII], Corollary 1.10, (b), that remains open.  They
are *not* assumed anywhere: the only assumption of the reduction is the named
proposition PsiCnsH2LimitComparison p.

## Not run

Full lake build of the project, comparator, and independent source-semantics
review are not part of this file.  The ported modules are compiled from
tmp/local-cft-port/local-class-field-theory-main into the project library;
the SHA/EXIT records are reported with the task.
-/

import LocalClassFieldTheory.Brauer.H2ZHat
import tmp.sheaf.xif.paper.S2036ActualPsiCnsM234Actual

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual

namespace LeanFormal.IUT.XiFPaper.S2091H2ZhatActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The two models of Ẑ -/

/-- S2036's Zhat and the port's Brauer.ZHat are the same subtype of ∏_(n > 0) ℤ/n
(same carrier, same compatibility predicate), so they are multiplicatively
isomorphic.  This is the transport of the target of the (M3) normalization
between the two formalizations. -/
noncomputable def zhatMulEquivBrauer : Multiplicative Zhat ≃* Multiplicative Brauer.ZHat :=
  MulEquiv.refl _

/-- The actual local absolute Galois group Gv p of S2000 is definitionally the
automorphism group of AlgebraicClosure ℚ_[p] over ℚ_[p] used by the ported
computation. -/
theorem gv_eq_absoluteGalois :
    Gv p = (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) := rfl

/-! ## 2. The ported computation H²(ℚ_p, Ẑ(1)) ≃ Ẑ -/

/-- **The ported H²(K, Ẑ(1)) ≃ Ẑ at the actual local field.**  This is
PadicField.h2ZHatOneEquiv of the external local class field theory
formalization at K = ℚ_[p], Ω = AlgebraicClosure ℚ_[p], composed with the
identification Brauer.ZHat ≃ Zhat of S2036's Ẑ. -/
noncomputable def h2ZHatOneEquiv_of_port :
    Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃* Multiplicative Zhat :=
  (PadicField.h2ZHatOneEquiv (p := p) (K := ℚ_[p]) (Ω := AlgebraicClosure ℚ_[p])).trans
    (zhatMulEquivBrauer).symm

/-- Existence form of the ported computation. -/
theorem nonempty_h2ZHatOneEquiv_of_port :
    Nonempty (Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
      Multiplicative Zhat) :=
  ⟨h2ZHatOneEquiv_of_port p⟩

/-- The value of the transported isomorphism on the n-th projection: this records
that the isomorphism is the limit of the cyclotomic rigidity isomorphisms
h2MuEquiv, not an arbitrary multiplicative equivalence. -/
theorem h2ZHatOneEquiv_of_port_apply
    (x : Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p])) (n : ℕ+) :
    ((Multiplicative.toAdd (h2ZHatOneEquiv_of_port p x) : Brauer.ZHat) : ∀ n : ℕ+, ZMod n) n =
      Multiplicative.toAdd
        (PadicField.h2MuEquiv p ℚ_[p] (AlgebraicClosure ℚ_[p]) n.pos
          (Brauer.H2ZHatOne.proj n x)) :=
  rfl

/-- **Br(ℚ_p) ≃ ℚ/ℤ**: the invariant map of local class field theory at the
actual local field of the project.  This is the Br(k_v) = Q/Z input of the (M4)
layer, proved in the external formalization (Brauer/Invariant.lean) and cited
here on the project's actual local field. -/
noncomputable def brEquivQZ :
    Brauer.Br ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃* Multiplicative Brauer.QZ :=
  PadicField.invEquiv (p := p) (K := ℚ_[p]) (Ω := AlgebraicClosure ℚ_[p])

/-- **Cyclotomic rigidity at the actual local field**: the n-torsion H²(ℚ_p, μ_n)
is ℤ/n.  This is the level input of the ported limit computation. -/
noncomputable def h2MuEquiv_actual (n : ℕ) (hn : 0 < n) :
    Brauer.H2Mu ℚ_[p] (AlgebraicClosure ℚ_[p]) n ≃* Multiplicative (ZMod n) :=
  PadicField.h2MuEquiv p ℚ_[p] (AlgebraicClosure ℚ_[p]) hn

/-! ## 3. The exact first missing: the cochain-model comparison -/

/-- **The exact first missing.**  The actual continuous H² of G_v with
coefficients in the actual cyclotome Hom(ℚ/ℤ, (O^tri)ˣ) (S2036's PsiCnsH2)
coincides with the inverse limit of the finite-level H²'s with coefficients in
the n-th roots of unity (the port's H2ZHatOne).

This is a proposition, not an assumption field of any structure and not a
weakened restatement of the conclusion: the theorem
PsiCnsH2Normalization_iff_limitComparison proves that it is *equivalent* to
(M3).  Its proof is the missing comparison of the two cochain models described
in the module docstring. -/
def PsiCnsH2LimitComparison (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  Nonempty (PsiCnsH2 p ≃* Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]))

/-- **(M3) from the cochain-model comparison and the ported computation.** -/
theorem PsiCnsH2Normalization_of_limitComparison (h : PsiCnsH2LimitComparison p) :
    PsiCnsH2Normalization p := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (h2ZHatOneEquiv_of_port p)⟩

/-- Conversely, (M3) yields the cochain-model comparison (through the ported
computation). -/
theorem limitComparison_of_PsiCnsH2Normalization (h : PsiCnsH2Normalization p) :
    PsiCnsH2LimitComparison p := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (h2ZHatOneEquiv_of_port p).symm⟩

/-- **The comparison is exactly (M3).**  Neither direction weakens the target:
the proposition PsiCnsH2LimitComparison is equivalent to S2036's
PsiCnsH2Normalization, the difference between the two being the ported
computation H²(ℚ_p, Ẑ(1)) ≃ Ẑ. -/
theorem PsiCnsH2Normalization_iff_limitComparison :
    PsiCnsH2Normalization p ↔ PsiCnsH2LimitComparison p :=
  ⟨limitComparison_of_PsiCnsH2Normalization p,
    PsiCnsH2Normalization_of_limitComparison p⟩

/-! ## 4. Assembly of the layered Corollary 1.10, (b) statement -/

/-- **[AbsTopIII], Corollary 1.10, (b), assembled**: the local Artin layer (M2),
the comparison for the H²-normalization, and the normalized-surjection layer
(M4) give the three missing layers of the corollary on the actual carriers. -/
theorem Cor110bLayersMissing_of_M2_of_comparison_of_M4
    (hM2 : M2FirstMissing p)
    (hH2 : PsiCnsH2LimitComparison p)
    (hM4 : PsiCnsKummerNormalization p) :
    Cor110bLayersMissing p :=
  ⟨hM2, PsiCnsH2Normalization_of_limitComparison p hH2, hM4⟩

/-! ## 5. Inventory of the ported declarations used -/

section PortInventory

#check @PadicField.h2ZHatOneEquiv
#check @PadicField.h2MuEquiv
#check @PadicField.invEquiv
#check @Brauer.toBr_injective
#check @Brauer.mem_range_toBr_iff
#check @Brauer.H2ZHatOne
#check @Brauer.H2ZHatOne.proj
#check @Brauer.h2MuPow

end PortInventory

/-! ## 6. Axiom probes -/

#print axioms zhatMulEquivBrauer
#print axioms brEquivQZ
#print axioms h2MuEquiv_actual
#print axioms gv_eq_absoluteGalois
#print axioms h2ZHatOneEquiv_of_port
#print axioms h2ZHatOneEquiv_of_port_apply
#print axioms PsiCnsH2Normalization_of_limitComparison
#print axioms limitComparison_of_PsiCnsH2Normalization
#print axioms PsiCnsH2Normalization_iff_limitComparison
#print axioms Cor110bLayersMissing_of_M2_of_comparison_of_M4

end LeanFormal.IUT.XiFPaper.S2091H2ZhatActual
