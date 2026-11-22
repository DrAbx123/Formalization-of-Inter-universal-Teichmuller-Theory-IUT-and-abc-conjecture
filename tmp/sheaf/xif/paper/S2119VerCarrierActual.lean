import tmp.sheaf.xif.paper.S2113M2bTransferActual

/-!
# S2119: M2b(B) -- the Verlagerung carrier comparison is closed

Layer: **O** (original Theta-link / q-pilot).  Consumer: S2113's
'VerCarrierComparison', and through it the M2b transfer bridge of
S2113/S2024/S2027.

S2113 localized item (B) of M2b as follows.  'PadicField.ver' is stated for an
intermediate field 'K' : IntermediateField K Ω', so to use it on the extension
'L_H / L_K' of fixed fields one must regard 'L_H = FixedField H' as an
intermediate field of 'Ω / L_K'.  S2113 built such a field by hand ('FH H h')
and recorded that no lemma identifies its Galois group with S2027's
'Gal(maximalAbelianExtension H / localField H)'.

This file proves that comparison.  The construction is the canonical one:

  K' h := Subfield.extendScalars
    (F := (FixedField p K).toSubfield)
    (E := (FixedField p H).toSubfield)
    (fixedField_le p h).

Its carrier is literally 'FixedField p H', and its base is literally
'↥((FixedField p K).toSubfield)', which is definitionally 'localField p K'.
The two instances needed by 'PadicField.ver' are supplied:

* 'K'_algebra : Algebra (localField p K) ↥(K' h)' (definitionally the
  canonical inclusion);
* 'K'_finiteDimensional : FiniteDimensional (localField p K) ↥(K' h)'.

The latter is not a new arithmetic input: the fixed field 'L_H' is finite over
'ℚ_[p]' (S2006), and 'Module.Finite.of_restrictScalars_finite' transports this
along 'ℚ_[p] -> localField p K'.  Equivalently, 'Index p' is an open subgroup,
so 'H' has finite index in 'K'; only the finite-dimensionality over 'ℚ_[p]' is
needed for the instance.

With these instances, 'PadicField.ver p (K' h)' is a genuine map

  Gal(Ω / localField p K) ->* Gal(maxAbelian (K' h) Ω / K' h).

The remaining subtlety is not mathematical but definitional: the base fields
'↥(K' h)' and 'localField p H' are definitionally equal, and so are the two
'maxAbelian' fields as subsets of 'Ω', but their 'Algebra' instance arguments
are not interchangeable at 'instances' transparency when an 'AlgEquiv' term is
passed around.  We therefore provide the explicit identity transport

  galK'EquivLocal h :
    Gal(maxAbelian (K' h) Ω / K' h) ≃*
    Gal(maxAbelian (localField p H) Ω / localField p H)

(the underlying automorphism is unchanged).  Composing with S2089's

  galoisGroupEquiv H :
    Gal(maxAbelian (localField p H) Ω / localField p H) ≃*
    Gal(maximalAbelianExtension H / localField H)

gives the comparison with S2027's carrier.  Consequently:

* 'verCarrierComparison' proves S2113's 'VerCarrierComparison' unconditionally;
  (B) is no longer a missing API.
* 'verS2027 h' is the transfer transported to S2027's carrier.
* 'artinTransfer_S2027' is S2113's 'artinTransfer_fixedField' after the
  transport, i.e. the norm side of M2b with target
  'Gal(maximalAbelianExtension H / localField H)'.

## Exact first missing after this file

The carrier comparison (B) is closed.  The remaining input for M2b is (A),
S2113's 'TransferBridge': the comparison of the abstract Verlagerung
'verlagerungOpen p h' (transported by 'kappa') with the Galois norm/Artin
transfer on roots of unity.  It is not assumed, not inhabited and not proved
here.  The third item of S2113, the 'Nonempty.some' choice in S2098, is
unchanged.

No 'sorry', 'admit', new axiom or fabricated inhabitant is used.  The axiom
probes at the end show only 'propext', 'Classical.choice', 'Quot.sound'.

## Not run

Full Project build, target comparator, independent review.
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual
open LeanFormal.IUT.XiFPaper.S2098M2aCoreActual
open LeanFormal.IUT.XiFPaper.S2113M2bTransferActual
open IntermediateField

namespace LeanFormal.IUT.XiFPaper.S2119VerCarrierActual

variable {p : Nat} [Fact (Nat.Prime p)]

local notation "Ω" => AlgebraicClosure ℚ_[p]

/-! ## 1. The canonical extension 'L_H / L_K' -/

/-- The fixed field 'L_H' regarded as an intermediate field of 'Ω / L_K',
via 'Subfield.extendScalars'.  The carrier is 'FixedField p H' and the base is
the subfield '(FixedField p K).toSubfield', definitionally 'localField p K'. -/
noncomputable def K' {H K : Index p} (h : H ≤ K) :
    IntermediateField (localField p K) Ω :=
  Subfield.extendScalars
    (F := (LocalIntegralUnitKummerInjectivity.FixedField p K).toSubfield)
    (E := (LocalIntegralUnitKummerInjectivity.FixedField p H).toSubfield)
    (by
      intro x hx
      exact fixedField_le p h hx)

/-- The canonical construction agrees definitionally with S2113's hand-built
'FH'. -/
theorem K'_eq_FH {H K : Index p} (h : H ≤ K) :
    K' (p := p) h = FH H h := rfl

/-- The canonical 'localField p K'-algebra structure on '↥(K' h)'.  It is the
restriction of the canonical '↥((FixedField p K).toSubfield)'-algebra
structure along the definitional equality of the two base fields. -/
instance K'_algebra {H K : Index p} (h : H ≤ K) :
    Algebra (localField p K) ↥(K' (p := p) h) :=
  inferInstanceAs
    (Algebra ↥((LocalIntegralUnitKummerInjectivity.FixedField p K).toSubfield)
      ↥(K' (p := p) h))

/-- **Finiteness of the extended fixed field over 'L_K'.**  The carrier is
'FixedField p H', finite over 'ℚ_[p]'; restriction of scalars along
'ℚ_[p] -> localField p K' gives finiteness over 'localField p K'. -/
instance K'_finiteDimensional {H K : Index p} (h : H ≤ K) :
    FiniteDimensional (localField p K) ↥(K' (p := p) h) := by
  haveI : Module.Finite ℚ_[p] ↥(K' (p := p) h) := by
    change Module.Finite ℚ_[p] (localField p H)
    infer_instance
  exact Module.Finite.of_restrictScalars_finite ℚ_[p] (localField p K)
    ↥(K' (p := p) h)

/-! ## 2. The explicit carrier transport -/

/-- The identity on the underlying automorphisms, between the 'K''-carrier and
the 'localField p H'-carrier.  The types are definitionally equal, but the
'Algebra' instance arguments of the two 'AlgEquiv' types are not
interchangeable at 'instances' transparency; this is the transport lemma that
the earlier package recorded as missing. -/
noncomputable def galK'EquivLocal {H K : Index p} (h : H ≤ K) :
    Gal(↥(PadicField.maxAbelian (↥(K' (p := p) h)) Ω) / ↥(K' (p := p) h)) ≃*
      Gal(↥(PadicField.maxAbelian (localField p H) Ω) / localField p H) where
  toFun σ := σ
  invFun σ := σ
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The comparison of the 'K''-carrier with S2027's maximal abelian
extension, obtained from 'galK'EquivLocal' and S2089's 'galoisGroupEquiv'. -/
theorem verCarrierComparison_K' {H K : Index p} (h : H ≤ K) :
    Nonempty
      (Gal(↥(PadicField.maxAbelian (↥(K' (p := p) h)) Ω) / ↥(K' (p := p) h)) ≃*
        Gal(↥(maximalAbelianExtension p H) / localField p H)) :=
  ⟨(galK'EquivLocal (p := p) h).trans (galoisGroupEquiv H)⟩

/-- **S2113's 'VerCarrierComparison' is true.**  No hypothesis is needed: for
'H ≤ K' the two Galois groups are the same group of automorphisms of the same
subfield of 'Ω', and 'galoisGroupEquiv H' identifies the first with S2027's
carrier. -/
theorem verCarrierComparison :
    S2113M2bTransferActual.VerCarrierComparison (p := p) := by
  intro H K h
  exact ⟨(galK'EquivLocal (p := p) h).trans (galoisGroupEquiv H)⟩

/-! ## 3. 'PadicField.ver' on the S2027 carrier -/

/-- **The transfer transported to S2027's carrier.**  This is
'PadicField.ver p (K' h)' composed with the carrier transport and S2089's
'galoisGroupEquiv H'. -/
noncomputable def verS2027 {H K : Index p} (h : H ≤ K) :
    Gal(Ω / localField p K) →*
      Gal(↥(maximalAbelianExtension p H) / localField p H) where
  toFun g :=
    galoisGroupEquiv H
      ((galK'EquivLocal (p := p) h) (PadicField.ver p (K' (p := p) h) g))
  map_one' := by
    simp only [map_one]
  map_mul' g g' := by
    simp only [map_mul]

/-- Computation rule for the transported transfer. -/
theorem verS2027_apply {H K : Index p} (h : H ≤ K)
    (g : Gal(Ω / localField p K)) :
    verS2027 (p := p) h g =
      galoisGroupEquiv H
        ((galK'EquivLocal (p := p) h) (PadicField.ver p (K' (p := p) h) g)) := rfl

/-- **The norm side of M2b on S2027's carrier.**  This is
'artinTransfer_fixedField' of S2113 after the carrier transport: for a root of
unity 'y' of 'L_K' and a lift 'g' of 'artin_K(y)', the Artin map of the
inclusion 'L_K ⊆ L_H' is the transported Verlagerung in
'Gal(maximalAbelianExtension H / localField H)'. -/
theorem artinTransfer_S2027 {H K : Index p} (h : H ≤ K) (y : mu p K)
    (g : localGaloisGroup p K)
    (hg : AlgEquiv.restrictNormalHom
        (PadicField.maxAbelian (localField p K) (AlgebraicClosure ℚ_[p])) g =
      PadicField.artin p (localField p K) (AlgebraicClosure ℚ_[p]) y) :
    galoisGroupEquiv H
      ((galK'EquivLocal (p := p) h)
        (PadicField.artin p (↥(K' (p := p) h)) (AlgebraicClosure ℚ_[p])
          (Units.map
            (algebraMap (localField p K) (↥(K' (p := p) h)))
            (y : (localField p K)ˣ)))) =
      verS2027 (p := p) h g := by
  rw [verS2027_apply]
  apply_fun (galoisGroupEquiv H).symm
  exact congrArg (galK'EquivLocal (p := p) h)
    (artinTransfer_fixedField (p := p) h y g hg)

/-! ## 4. What remains -/

/-- The exact remaining input after (B).  This is S2113's 'TransferBridge',
restated here only to make the boundary of the present package explicit.  It is
not assumed and no inhabitant is produced. -/
def M2bFirstMissing : Prop :=
  S2113M2bTransferActual.TransferBridge (p := p)

/-! ## 5. Axiom probes -/

#print axioms K'
#print axioms K'_eq_FH
#print axioms K'_algebra
#print axioms K'_finiteDimensional
#print axioms galK'EquivLocal
#print axioms verCarrierComparison_K'
#print axioms verCarrierComparison
#print axioms verS2027
#print axioms verS2027_apply
#print axioms artinTransfer_S2027

end LeanFormal.IUT.XiFPaper.S2119VerCarrierActual

end
