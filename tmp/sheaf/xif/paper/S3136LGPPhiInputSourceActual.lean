import tmp.sheaf.xif.paper.LGPPhiInputActual
import tmp.sheaf.xif.paper.LGPPhiInputFromAlgebraicClosureActual
import tmp.sheaf.xif.paper.LGPThetaActionActual
import tmp.sheaf.xif.paper.PaperSymbolTypesActual

/-! # Stage-4 host: actual LGP Phi/Input source data (IUT III, §3)

Source anchors:
* IUT III, Prop. 3.4, (ii) (pp. 102--103): the local LGP-monoids
  `Ψ_FLGP(†HT^Θ±ellNF)_v` with their label-j components, for v in V_bad;
* IUT III, Prop. 3.7, (ii), (iii), (iv), (v) (pp. 108--112): the local
  fractional ideals `J_v`, the global realified LGP-Frobenioid `C^⊩_LGP`,
  its lgp/×μ versions, and the realified product embeddings;
* IUT III, Def. 3.8, (i) (p. 112): the Theta-pilot and q-pilot objects of `C^⊩_LGP`;
* IUT II, Cor. 4.8, (ii), (iii); Cor. 4.10, (i), (ii): the Frobenioid
  isomorphisms `(F^⊛_mod) ≅ (F^⊛_MOD)` and the realified F^⊩-prime-strips.

What is constructed here from actual source data:
* the 2l-th root normalization law for the actual algebraic-closure theta
  values (theta value^(2l) = q^{j^2}, IUT III, Prop. 3.4, (ii));
* the actual LGP prime index `V_bad × {1,...,l*}` and its actual theta
  divisor exponents `j^2 * ord_v(q_v)` (nonvanishing by the source q_v
  theory, S2238/S2321);
* the free commutative divisor cone on the LGP prime index together with the
  actual prime divisors and the carrier interface `LGPXMuCarrier` for the
  lattice stream.

Exact object-level gap (NOT discharged, recorded with source references):
the local LGP-monoids / local fractional ideals `J_v`, the Frobenioid
isomorphisms that transport `C^⊩_gau` to `C^⊩_LGP`, and hence the LGP
Frobenioid presentation Phi/Input layer.  No value-layer surrogate is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.LGPPhiInputActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The 2l-th root normalization of the LGP theta values -/

/-- The actual algebraic-closure LGP theta value at label j satisfies the source
2l-th root normalization: its (2l)-th power is the j^2-th power of the actual
qV unit (IUT III, Prop. 3.4, (ii); the 2l-th root normalization of
`LGPPhiInputActual`). -/
theorem lgpThetaValueAlgClosed_pow_twoL
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    lgpThetaValueAlgClosed T b j ^ twoLExponent l =
      unitToAlgClosed (qVUnit T b) ^ (gaussExponent j.1).toNat := by
  unfold lgpThetaValueAlgClosed
  rw [← pow_mul, Nat.mul_comm, pow_mul, lgpTwoLthRootAlgClosed_pow]

/-- The actual completion-level 2l-th root normalization for the LGP roots
(IUT III, Prop. 3.4, (ii)): a compatible NatRootSystem gives a root whose
(2l)-th power is the actual qV unit. -/
theorem lgpTwoLthRoot_pow_twoL
    (b : Bad (nativePlaceSelection T)) (R : NatRootSystem (qVUnit T b)) :
    lgpTwoLthRoot T b R ^ twoLExponent l = qVUnit T b :=
  lgpTwoLthRoot_pow T b R

/-! ## 2. Actual LGP prime index and theta divisor cone -/

/-- The actual LGP prime index: bad places v times positive theta labels
j = 1,...,l* (IUT III, Prop. 3.4, (ii): one label-j component per v in V_bad). -/
abbrev LGPPrimeIndex : Type := Bad (nativePlaceSelection T) × PaperThetaLabel l

/-- The free commutative divisor cone on the actual LGP prime index. -/
abbrev LGPThetaDivisorCone : Type := LGPPrimeIndex (l := l) T →₀ ℕ

/-- The actual gaussian exponent weight j^2 of a positive theta label. -/
def lgpThetaLabelWeight (j : PaperThetaLabel l) : ℕ :=
  (gaussExponent j.1.1).toNat

/-- The gaussian weight is the square of the integer label. -/
theorem lgpThetaLabelWeight_eq_sq (j : PaperThetaLabel l) :
    lgpThetaLabelWeight j = (j.1.1 ^ 2).toNat := rfl

/-- The gaussian weight of a positive label is positive. -/
theorem lgpThetaLabelWeight_pos (j : PaperThetaLabel l) :
    0 < lgpThetaLabelWeight j := by
  unfold lgpThetaLabelWeight
  have hnonneg : 0 ≤ gaussExponent j.1.1 := gaussExponent_nonneg j.1.1
  have hne : gaussExponent j.1.1 ≠ 0 := by
    unfold gaussExponent
    exact pow_ne_zero 2 (ne_of_gt j.2)
  have hne' : (gaussExponent j.1.1).toNat ≠ 0 := by
    intro h
    have hcast : ((gaussExponent j.1.1).toNat : ℤ) = gaussExponent j.1.1 :=
      Int.toNat_of_nonneg hnonneg
    rw [h] at hcast
    exact hne hcast.symm
  exact Nat.pos_of_ne_zero hne'

/-- The actual theta-value divisor exponent at the LGP prime (v, j):
j^2 times the actual order of q_v at v (nonvanishing; the qV data of
`LGPPhiInputActual`). -/
def lgpThetaDivisorExponent (p : LGPPrimeIndex (l := l) T) : ℕ :=
  lgpThetaLabelWeight p.2 * lgpQVDivisorExponent T p.1

/-- The actual theta divisor exponent is positive at every LGP prime. -/
theorem lgpThetaDivisorExponent_pos (p : LGPPrimeIndex (l := l) T) :
    0 < lgpThetaDivisorExponent T p :=
  Nat.mul_pos (lgpThetaLabelWeight_pos p.2) (lgpQVDivisorExponent_pos T p.1)

/-- The actual prime divisor in the LGP theta divisor cone: a single LGP prime
with its actual theta-value divisor exponent. -/
def lgpThetaPilotPrimeDivisor (p : LGPPrimeIndex (l := l) T) :
    LGPThetaDivisorCone (l := l) T :=
  Finsupp.single p 1

/-- Each actual LGP prime divisor is nonzero. -/
theorem lgpThetaPilotPrimeDivisor_ne_zero (p : LGPPrimeIndex (l := l) T) :
    lgpThetaPilotPrimeDivisor T p ≠ 0 := by
  intro h
  have h2 := congrArg (fun f : LGPThetaDivisorCone (l := l) T => f p) h
  simp only [lgpThetaPilotPrimeDivisor, Finsupp.single_eq_same,
    Finsupp.zero_apply] at h2
  exact one_ne_zero h2

/-! ## 3. The F^LGP × μ carrier interface for the lattice stream -/

/-- The actual carrier data for the F^LGP (and F^LGP×μ) Frobenioid layer:
a prime index (the bad places times positive theta labels), the free
commutative divisor cone on it, the actual prime divisors with their
theta-value divisor exponents, and nonvanishing.  This is the interface the
lattice stream can attach finite Kummer/thetas arrows to; it is the actual
divisor carrier, not the (missing) local fractional ideal presentation. -/
structure LGPXMuCarrier where
  /-- The prime index set (V_bad × {1,...,l*}). -/
  PrimeIndex : Type
  /-- The free commutative divisor cone on the prime index set. -/
  divisorCone : Type
  [addCommMonoid : AddCommMonoid divisorCone]
  /-- Cancellation in the divisor cone (integrality, [FrdI] Def. 1.1(i)). -/
  add_left_cancel : ∀ a b c : divisorCone, a + b = a + c → b = c
  /-- The prime divisor attached to each prime index. -/
  primeDivisor : PrimeIndex → divisorCone
  /-- The theta-value divisor exponent attached to each prime index. -/
  thetaExponent : PrimeIndex → ℕ
  thetaExponent_pos : ∀ p, 0 < thetaExponent p
  primeDivisor_ne_zero : ∀ p, primeDivisor p ≠ 0

attribute [instance] LGPXMuCarrier.addCommMonoid

/-- The actual F^LGP×μ carrier built from the actual q_v/theta data. -/
noncomputable def lgpXMuCarrierActual : LGPXMuCarrier where
  PrimeIndex := LGPPrimeIndex (l := l) T
  divisorCone := LGPThetaDivisorCone (l := l) T
  addCommMonoid := inferInstance
  add_left_cancel := by
    intro a b c h
    ext i
    have hi := congrArg (fun f : LGPThetaDivisorCone (l := l) T => f i) h
    simp only [Finsupp.add_apply] at hi
    omega
  primeDivisor := lgpThetaPilotPrimeDivisor T
  thetaExponent := lgpThetaDivisorExponent T
  thetaExponent_pos := lgpThetaDivisorExponent_pos T
  primeDivisor_ne_zero := lgpThetaPilotPrimeDivisor_ne_zero T

/-! ## 4. Exact Missing record (object level, with source references) -/

/-- Exact object-level gap for the LGP Phi/Input layer.  Each field names one
source object that is NOT constructed in the tree; no surrogate is used.

* `lgpLocalMonoid`: IUT III, Prop. 3.4, (ii) (pp. 102--103) — the local
  LGP-monoids `Ψ_FLGP(†HT^Θ±ellNF)_v` (subquotients of `log(A,αFv)` with the
  `G_v(αΠ_v)`-action), including the label-j components.
* `localFractionalIdeal`: IUT III, Prop. 3.7, (ii), (v) (pp. 108--112) — the
  local fractional ideals `J_v` generated by the monoid elements `Ψ_FLGP,v`,
  with Q-span the corresponding `IQ(A,αFv)`.
* `frobenioidIsomorphism`: IUT II, Cor. 4.8, (ii) (and IUT III, Prop. 3.7,
  (i), (ii)) — the Frobenioid isomorphisms `(F^⊛_mod) ≅ (F^⊛_MOD)` and the
  realifications `(F^⊛R_mod) ≅ (F^⊛R_MOD)` that transport the actual global
  model Frobenioid to the LGP one.
* `globalRealifiedLGPPresentation`: IUT III, Prop. 3.7, (iii) (p. 109),
  Def. 3.8, (i) (p. 112) — the global realified LGP-Frobenioid
  `C^⊩_LGP` (its `FrobenioidPresentation`/Phi/Input data and degree layer),
  obtained by applying the isomorphisms above to `C^⊩_gau`.
* `xMuLGPPresentation`: IUT III, Prop. 3.7, (iv), Def. 3.8, (ii) — the
  ×μ/lgp version `C^⊩_lgp` and the tautological isomorphisms
  `F^⊩_gau ≅ F^⊩_LGP ≅ F^⊩_lgp` of F^⊩-prime-strips.

The presentation itself is therefore not built from this file: only the actual
2l-th-root/theta divisor carrier and the exact missing objects are recorded. -/
structure LGPPhiInputSourceMissing where
  lgpLocalMonoid : Prop
  localFractionalIdeal : Prop
  frobenioidIsomorphism : Prop
  globalRealifiedLGPPresentation : Prop
  xMuLGPPresentation : Prop

/-- The exact LGP Phi/Input gap is the object-level record above. -/
def LGPPhiInputSourceGap : Prop := Nonempty LGPPhiInputSourceMissing

#check lgpThetaValueAlgClosed_pow_twoL
#check lgpTwoLthRoot_pow_twoL
#check lgpThetaLabelWeight_pos
#check lgpThetaDivisorExponent_pos
#check lgpThetaPilotPrimeDivisor_ne_zero
#check lgpXMuCarrierActual
#check LGPPhiInputSourceGap

end LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
end
