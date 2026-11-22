import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.QVFamGlobalProductCarrierActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

/-! # S2753 carrier transport: the Gaussian native-T obstruction and the exact
carrier gap

## Result

The fixed Gaussian arithmetic
`A = gaussianInitialThetaArithmeticData l` has `Fmod = F = K = GaussianField`
(the identity tower).  Definition 3.1(c) requires
`A.K ≃ₐ[A.F] galoisLTorsionKernelField l basis` together with the image of the
`l`-torsion representation containing `SL₂`.  Because `A.K = A.F`, the
kernel-field identification forces the kernel field to be the base field;
then the fixing subgroup is `⊤`, the representation is trivial, and the
`SL₂` containment fails (the transvection `[[1,1],[0,1]]` is nontrivial).
Hence there is no `SourceClauseC` over the Gaussian arithmetic, and therefore
no `T : SourceNativeInitialThetaData l` with
`T.arithmetic = gaussianInitialThetaArithmeticData l`.

Consequences for S2753/S2757:

* `S2753KEquiv` is only supplied under the inconsistent equality hypothesis;
  `S2753SourceKEquivGaussian` records the actual source-side defeq
  `(S2735Arithmetic fiveLabel).K = GaussianField`.
* `S2753CarrierMap` is not defined as a constant or null map.  It is defined
  from the exact missing datum `S2753CarrierTransportDatum`, an actual
  point/place realization of the fractional-ideal carrier in the mixed-prime
  qVFam tensor carrier with the q-pilot membership required by the bridge.
  No such map from `FractionalIdeal` to `qVFamTensorBlock` exists in the tree;
  the only existing point map is the S2588 rational-point map on ABC triples.

No arbitrary default carrier is introduced. -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.QVFamGlobalProductCarrierActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2753CarrierTransportActual

/-- The label `l = 5` used by the S2753 request. -/
def fiveLabel : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

theorem fiveLabel_value : fiveLabel.value = 5 := rfl

/-- The fixed Gaussian arithmetic of S2735. -/
abbrev S2753Arithmetic : InitialThetaArithmeticData fiveLabel :=
  gaussianInitialThetaArithmeticData fiveLabel

/-! ## The kernel-field obstruction -/

/-- If the base field `F` itself is `F`-algebra equivalent to an intermediate
field of `L`, then that intermediate field is the base field. -/
theorem intermediateField_eq_bot_of_algEquiv_self
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (K' : IntermediateField F L) (φ : F ≃ₐ[F] K') : K' = ⊥ := by
  apply le_antisymm
  · intro y hy
    rw [IntermediateField.mem_bot]
    refine ⟨φ.symm ⟨y, hy⟩, ?_⟩
    have h := φ.commutes (φ.symm ⟨y, hy⟩)
    have h' := congrArg (fun z : K' => (z : L)) h
    simpa using h'.symm
  · exact bot_le

/-- There is no clause (c) over the Gaussian arithmetic: the kernel-field
identification collapses to the base field, making the torsion representation
trivial, while the clause also requires the image to contain `SL₂`. -/
theorem noSourceClauseC_gaussian
    (l : PrimeGeFive)
    (S : SourceSignQuotientData (gaussianInitialThetaArithmeticData l))
    (C : SourceClauseA (gaussianInitialThetaArithmeticData l) S)
    (B : SourceClauseB (gaussianInitialThetaArithmeticData l) S C)
    (D : SourceClauseC (gaussianInitialThetaArithmeticData l) S C B) : False := by
  have hK : (gaussianInitialThetaArithmeticData l).curve.galoisLTorsionKernelField l
      D.torsion_basis = ⊥ :=
    intermediateField_eq_bot_of_algEquiv_self _ D.kernel_field_identification
  let f : SourceAbsoluteGalois (gaussianInitialThetaArithmeticData l) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
    (gaussianInitialThetaArithmeticData l).curve.galoisLTorsionMatrixRepresentation l
      D.torsion_basis
  have hker : f.ker = ⊤ := by
    have hfix := (gaussianInitialThetaArithmeticData l).curve.galoisLTorsionKernelField_fixingSubgroup
      l D.torsion_basis
    rw [hK, IntermediateField.fixingSubgroup_bot] at hfix
    simpa [f, PuncturedEllipticCurve.galoisLTorsionKernelSubgroup] using hfix.symm
  have hf : f = 1 := (MonoidHom.ker_eq_top_iff).mp hker
  let g : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) :=
    Matrix.SpecialLinearGroup.transvection (ι := Fin 2) (i := 0) (j := 1)
      (by decide) (1 : ZMod l.value)
  have hmem : Matrix.SpecialLinearGroup.toGL g ∈ f.range := by
    have h := D.image_contains_SL2
    rw [D.representation_eq_canonical] at h
    exact h (Subgroup.mem_map.mpr ⟨g, Subgroup.mem_top g, rfl⟩)
  have h1 : Matrix.SpecialLinearGroup.toGL g = 1 := by
    rcases MonoidHom.mem_range.mp hmem with ⟨x, hx⟩
    rw [hf] at hx
    simpa using hx.symm
  have hgval : (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) =
      1 + Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod l.value) := by
    dsimp [g]
    exact Matrix.SpecialLinearGroup.transvection_coe (by decide) 1
  have hmat : (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) = 1 := by
    have hcoer := congrArg (fun z : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) =>
      (z : Matrix (Fin 2) (Fin 2) (ZMod l.value))) h1
    simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hcoer
  have h01 : (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) 0 1 = 0 := by
    rw [hmat]
    rfl
  have hg01 : (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) 0 1 = 1 := by
    rw [hgval]
    simp
  rw [hg01] at h01
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  exact (one_ne_zero : (1 : ZMod l.value) ≠ 0) h01

/-- Transport of the clause-(c) emptiness along an equality of arithmetic
data.  `A'` is a variable, so the dependent elimination is legitimate; this
is the form used for a `SourceNativeInitialThetaData` whose `arithmetic` is a
projection. -/
theorem noSourceClauseC_of_eq
    (l : PrimeGeFive)
    (A' : InitialThetaArithmeticData l)
    (h : A' = gaussianInitialThetaArithmeticData l)
    (S : SourceSignQuotientData A')
    (C : SourceClauseA A' S)
    (B : SourceClauseB A' S C)
    (D : SourceClauseC A' S C B) : False := by
  cases h
  exact noSourceClauseC_gaussian l S C B D

/-- Exact first obstruction: no native initial-Theta datum can have the
Gaussian arithmetic. -/
theorem noGaussianNativeT_general
    (l : PrimeGeFive)
    (T : SourceNativeInitialThetaData l)
    (h : T.arithmetic = gaussianInitialThetaArithmeticData l) : False :=
  noSourceClauseC_of_eq l T.arithmetic h T.tuple.source T.clauseA T.clauseB T.clauseC

/-- The same obstruction for the completed source package, which is exactly
the input of `S2757CanonicalGaussianT`. -/
theorem noGaussianSourceCompletion_general
    (l : PrimeGeFive)
    (C : SourceCompletion l)
    (h : C.arithmetic = gaussianInitialThetaArithmeticData l) : False :=
  noSourceClauseC_of_eq l C.arithmetic h C.signQuotient.toSourceSignQuotientData
    C.clauseA C.clauseB C.clauseC

/-- S2753 label specialization: no `T` over `fiveLabel` has Gaussian
arithmetic. -/
theorem noGaussianNativeT
    (T : SourceNativeInitialThetaData fiveLabel)
    (h : T.arithmetic = gaussianInitialThetaArithmeticData fiveLabel) : False :=
  noGaussianNativeT_general fiveLabel T h

/-- S2753 label specialization for `SourceCompletion`. -/
theorem noGaussianSourceCompletion
    (C : SourceCompletion fiveLabel)
    (h : C.arithmetic = gaussianInitialThetaArithmeticData fiveLabel) : False :=
  noGaussianSourceCompletion_general fiveLabel C h

/-! ## K transport -/

/-- The actual source-side K transport: the Gaussian arithmetic's K is
definitionally `GaussianField`, so the identity ring equivalence is the
source K identification.  This is non-vacuous and does not need a native T. -/
noncomputable def S2753SourceKEquivGaussian :
    (S2735Arithmetic fiveLabel).K ≃+* GaussianField :=
  RingEquiv.refl _

theorem S2753SourceKEquivGaussian_apply
    (x : (S2735Arithmetic fiveLabel).K) :
    S2753SourceKEquivGaussian x = x := rfl

/-- Conditional S2753 K-equivalence for a hypothetical native T with Gaussian
arithmetic.  The equality hypothesis is inconsistent by
`noGaussianNativeT`; the definition records the exact defeq transport that
would be used. -/
noncomputable def S2753KEquiv
    (T0 : SourceNativeInitialThetaData fiveLabel)
    (h : T0.arithmetic = gaussianInitialThetaArithmeticData fiveLabel) :
    (S2735Arithmetic fiveLabel).K ≃+* T0.arithmetic.K :=
  h.symm ▸ RingEquiv.refl ((S2735Arithmetic fiveLabel).K)

theorem S2753KEquiv_def
    (T0 : SourceNativeInitialThetaData fiveLabel)
    (h : T0.arithmetic = gaussianInitialThetaArithmeticData fiveLabel) :
    S2753KEquiv T0 h =
      (h.symm ▸ RingEquiv.refl ((S2735Arithmetic fiveLabel).K)) := rfl

/-! ## The exact carrier-transport gap -/

/-- The exact missing object for S2753: an actual point/place realization of
the fractional-ideal line-bundle carrier in the mixed-prime qVFam tensor
carrier, sending the q-pilot line bundle into the global q-pilot region.  No
construction of such a map from `FractionalIdeal` to `qVFamTensorBlock` is
present in the tree; the S2720 bridge has only the S2588 rational-point map on
ABC triples, not a line-bundle point map. -/
structure S2753CarrierTransportDatum
    (T : SourceNativeInitialThetaData fiveLabel) where
  toCarrier : SourceLineBundle (A := S2735Arithmetic fiveLabel) →
    QVFamProductCarrier T
  qPilotLineBundle_mem : toCarrier (qPilotLineBundle fiveLabel) ∈
    globalQPilotRegion (T := T)

namespace S2753CarrierTransportDatum

variable {T : SourceNativeInitialThetaData fiveLabel}

theorem toCarrier_qPilot_mem (D : S2753CarrierTransportDatum T) :
    D.toCarrier (qPilotLineBundle fiveLabel) ∈ globalQPilotRegion (T := T) :=
  D.qPilotLineBundle_mem

end S2753CarrierTransportDatum

/-- The exact missing-object proposition: a line-bundle point/place
realization into the qVFam product carrier.  It is stated, not asserted. -/
def S2753CarrierTransportRequired
    (T : SourceNativeInitialThetaData fiveLabel) : Prop :=
  Nonempty (S2753CarrierTransportDatum T)

/-- The S2753 carrier map, conditional on the exact missing transport datum.
It is the datum's point/place realization, not a constant or null default. -/
noncomputable def S2753CarrierMap
    (T0 : SourceNativeInitialThetaData fiveLabel)
    (_h : T0.arithmetic = gaussianInitialThetaArithmeticData fiveLabel)
    (D : S2753CarrierTransportDatum T0) :
    SourceLineBundle (A := S2735Arithmetic fiveLabel) → QVFamProductCarrier T0 :=
  D.toCarrier

theorem S2753CarrierMap_apply
    (T0 : SourceNativeInitialThetaData fiveLabel)
    (h : T0.arithmetic = gaussianInitialThetaArithmeticData fiveLabel)
    (D : S2753CarrierTransportDatum T0)
    (I : SourceLineBundle (A := S2735Arithmetic fiveLabel)) :
    S2753CarrierMap T0 h D I = D.toCarrier I := rfl

theorem S2753CarrierMap_qPilot_mem
    (T0 : SourceNativeInitialThetaData fiveLabel)
    (h : T0.arithmetic = gaussianInitialThetaArithmeticData fiveLabel)
    (D : S2753CarrierTransportDatum T0) :
    S2753CarrierMap T0 h D (qPilotLineBundle fiveLabel) ∈ globalQPilotRegion (T := T0) :=
  D.qPilotLineBundle_mem

#check S2753SourceKEquivGaussian
#check S2753KEquiv
#check S2753CarrierTransportDatum
#check S2753CarrierTransportRequired
#check S2753CarrierMap
#check noGaussianNativeT_general
#check noGaussianSourceCompletion_general
#check noGaussianNativeT
#check noGaussianSourceCompletion

#print axioms noSourceClauseC_gaussian
#print axioms noGaussianNativeT_general
#print axioms noGaussianSourceCompletion_general
#print axioms S2753KEquiv
#print axioms S2753CarrierMap

end S2753CarrierTransportActual
end XiFPaper
end IUT
end LeanFormal
end
