/-
  # The actual log-Kummer map from principal units to the log-shell

  Task task-88 (Foundation F6e).  At the actual finite place of the concrete
  Example 3.6 carrier, this module constructs the actual log-Kummer map from
  the principal units H to the actual principal-unit log-shell:

  * logKummer : H -> principalUnitLogShell is defined by x |-> unitLog(x), the
    actual p-adic logarithm of the tree, taking values in the actual shell by
    construction (principalUnitLogShell is the image of unitLog on H).
  * It is additive on the additive group of H (logKummerAddHom), and it is
    surjective onto the shell by definition of the shell as that image.
  * Its kernel is exactly the torsion locus of H: logKummer x = 0 iff x is of
    finite order (tree unitLog kernel computation), and the kernel set is the
    torsion subgroup of H.
  * It commutes with the actual p-power Frobenius and the p-fold scaling:
    logKummer(x^p) = p * logKummer(x), and the induced map on the shell is
    exactly principalUnitLogShellFrobenius (the p-fold scaling endomorphism of
    the previous module).
  * The realified task-21 unit value kernel of the p-power Frobenius is p times
    the realification (where available).

  The non-source parts of the frozen source Frobenius/log-Kummer card are
  populated by actual tree data: treeSourceFrobeniusLogKummerCard constructs the
  structural Frobenius/log-Kummer/commutation data from the actual principal
  units, log-shell and p-power maps.  The identification of this data with the
  source's Frobenius/log-Kummer operator is NOT constructed and remains frozen
  as SourceFrobeniusLogKummerIdentificationCard.  No fake map is substituted.
  No theta-pilot/q-pilot/Tate claim is made.

  Source correspondence: IUT III, Definition 1.1 and Remark 1.2.2 (log-shell
  and Frobenius action); IUT III, Proposition 1.2.
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellFrobeniusAction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace LogKummerMap

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellFrobeniusAction
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

local instance gaussianPolynomialIrreducibleFactLogKummer :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactLogKummer : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactLogKummer (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The actual log-Kummer map and its elementary properties -/

/-- The actual log-Kummer map from the principal units H to the actual
principal-unit log-shell: x |-> unitLog(x). -/
noncomputable def logKummer :
    principalUnits (K := concreteLogShellField) → principalUnitLogShell :=
  fun u =>
    ⟨unitLog (K := concreteLogShellField)
        (u : (Integers concreteLogShellField)ˣ),
      (principalUnitLogShell_mem_iff _).mpr ⟨u, rfl⟩⟩

@[simp] theorem logKummer_apply_coe
    (u : principalUnits (K := concreteLogShellField)) :
    (logKummer u : concreteLogShellField) =
      unitLog (K := concreteLogShellField)
        (u : (Integers concreteLogShellField)ˣ) :=
  rfl

/-- The log-Kummer map is surjective onto the actual log-shell: the shell is by
construction the image of the logarithm on H. -/
theorem logKummer_surjective :
    Function.Surjective logKummer := by
  rintro ⟨x, hx⟩
  obtain ⟨u, hu⟩ := (principalUnitLogShell_mem_iff x).mp hx
  exact ⟨u, Subtype.ext hu⟩

/-- The log-Kummer map kills the unit principal unit. -/
theorem logKummer_one :
    logKummer (1 : principalUnits (K := concreteLogShellField)) = 0 := by
  apply Subtype.ext
  simp [logKummer, unitLog_one (K := concreteLogShellField) (p := concreteRationalPrime)]

/-- The log-Kummer map is multiplicative on the principal-unit group. -/
theorem logKummer_mul
    (u v : principalUnits (K := concreteLogShellField)) :
    logKummer (u * v) = logKummer u + logKummer v := by
  apply Subtype.ext
  simp [logKummer, unitLog_mul (K := concreteLogShellField) (p := concreteRationalPrime)]

/-- The actual log-Kummer map as a monoid homomorphism from the principal-unit
group to the multiplicative form of the log-shell. -/
noncomputable def logKummerHom :
    principalUnits (K := concreteLogShellField) →*
      Multiplicative principalUnitLogShell where
  toFun u := Multiplicative.ofAdd (logKummer u)
  map_one' := by
    rw [logKummer_one]
    rfl
  map_mul' := by
    intro u v
    rw [logKummer_mul]
    rfl

@[simp] theorem logKummerHom_apply
    (u : principalUnits (K := concreteLogShellField)) :
    logKummerHom u = Multiplicative.ofAdd (logKummer u) :=
  rfl

/-- The log-Kummer kernel is the zero locus of the actual logarithm. -/
theorem logKummer_eq_zero_iff_unitLog_eq_zero
    (u : principalUnits (K := concreteLogShellField)) :
    logKummer u = 0 ↔
      unitLog (K := concreteLogShellField)
        (u : (Integers concreteLogShellField)ˣ) = 0 := by
  rw [Subtype.ext_iff]
  rfl

/-- The actual logarithm kills exactly the finite-order principal units. -/
theorem logKummer_eq_zero_iff_isOfFinOrder
    (u : principalUnits (K := concreteLogShellField)) :
    logKummer u = 0 ↔ IsOfFinOrder u := by
  rw [logKummer_eq_zero_iff_unitLog_eq_zero]
  constructor
  · intro h
    have hcoe :
        IsOfFinOrder (u : (Integers concreteLogShellField)ˣ) :=
      (unitLog_eq_zero_iff_isOfFinOrder (K := concreteLogShellField)
        (p := concreteRationalPrime) (u : (Integers concreteLogShellField)ˣ)).mp h
    rw [isOfFinOrder_iff_pow_eq_one] at hcoe ⊢
    obtain ⟨n, hn, hpow⟩ := hcoe
    exact ⟨n, hn, Subtype.ext hpow⟩
  · intro h
    rw [isOfFinOrder_iff_pow_eq_one] at h
    obtain ⟨n, hn, hpow⟩ := h
    have hcoe : (u : (Integers concreteLogShellField)ˣ) ^ n = 1 := by
      simpa using congrArg
        (fun x : principalUnits (K := concreteLogShellField) =>
          (x : (Integers concreteLogShellField)ˣ)) hpow
    exact (unitLog_eq_zero_iff_isOfFinOrder (K := concreteLogShellField)
      (p := concreteRationalPrime) (u : (Integers concreteLogShellField)ˣ)).mpr
      ((isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, hcoe⟩)

/-- The kernel set of the log-Kummer map is exactly the torsion subgroup of the
principal units H. -/
theorem logKummer_kernel_eq_torsion :
    {u : principalUnits (K := concreteLogShellField) | logKummer u = 0} =
      (CommGroup.torsion (principalUnits (K := concreteLogShellField)) :
        Set (principalUnits (K := concreteLogShellField))) := by
  ext u
  rw [Set.mem_setOf_eq, logKummer_eq_zero_iff_isOfFinOrder]
  exact (CommGroup.mem_torsion u).symm

/-- The kernel of the log-Kummer homomorphism is exactly the torsion subgroup
of the principal units H. -/
theorem logKummerHom_ker :
    logKummerHom.ker =
      CommGroup.torsion (principalUnits (K := concreteLogShellField)) := by
  ext u
  rw [MonoidHom.mem_ker, CommGroup.mem_torsion, logKummerHom_apply]
  have h : Multiplicative.ofAdd (logKummer u) = 1 ↔ logKummer u = 0 := by simp
  rw [h, logKummer_eq_zero_iff_isOfFinOrder]


/-! ## 2. Commutation with the p-power Frobenius and p-fold scaling -/

/-- **Frobenius commutation of the log-Kummer map.**  logKummer(x^p) is the
p-fold scaling of logKummer(x). -/
theorem logKummer_commutes_frobenius
    (u : principalUnits (K := concreteLogShellField)) :
    logKummer (principalUnitFrobenius u) =
      principalUnitLogShellFrobenius (logKummer u) := by
  apply Subtype.ext
  rw [logKummer_apply_coe, principalUnitLogShellFrobenius_apply,
    logKummer_apply_coe, unitLog_principalUnitFrobenius_log]

/-- The induced map on the log-shell is exactly the p-fold scaling: for every
principal unit, applying logKummer after the p-power Frobenius equals applying
the shell Frobenius after logKummer. -/
theorem logKummer_frobenius_scaling
    (u : principalUnits (K := concreteLogShellField)) :
    logKummer (principalUnitFrobenius u) =
      ⟨(concreteRationalPrime : concreteLogShellField) * (logKummer u :
          concreteLogShellField),
        principalUnitLogShell_p_mul_mem (logKummer u).2⟩ := by
  apply Subtype.ext
  rw [logKummer_apply_coe, unitLog_principalUnitFrobenius_log]
  rfl

/-! ## 3. Packaging the actual log-Kummer data -/

/-- The actual log-Kummer data package: the principal units, their log-shell,
the actual log-Kummer map, the p-power Frobenius and the p-fold scaling on the
shell, with proved surjectivity and Frobenius commutation. -/
structure LogKummerData where
  /-- The principal-unit group H. -/
  H : Type
  /-- The group structure on H. -/
  [groupH : Group H]
  /-- The log-shell. -/
  logShell : Type
  /-- The additive group structure on the log-shell. -/
  [addCommGroupLogShell : AddCommGroup logShell]
  /-- The actual log-Kummer map. -/
  logKummer : H → logShell
  /-- The p-power Frobenius on H. -/
  frobenius : H → H
  /-- The p-fold scaling on the log-shell. -/
  pScaling : logShell → logShell
  /-- The log-Kummer map is surjective onto the shell. -/
  surjective : Function.Surjective logKummer
  /-- The log-Kummer map commutes with Frobenius and p-fold scaling. -/
  commutes : ∀ h : H, logKummer (frobenius h) = pScaling (logKummer h)

/-- The actual log-Kummer data built from the concrete principal units, log-shell
and p-power maps. -/
noncomputable def logKummerData : LogKummerData where
  H := principalUnits (K := concreteLogShellField)
  logShell := principalUnitLogShell
  logKummer := logKummer
  frobenius := principalUnitFrobenius
  pScaling := principalUnitLogShellFrobenius
  surjective := logKummer_surjective
  commutes := logKummer_commutes_frobenius

@[simp] theorem logKummerData_H :
    logKummerData.H = principalUnits (K := concreteLogShellField) :=
  rfl

@[simp] theorem logKummerData_logShell :
    logKummerData.logShell = principalUnitLogShell :=
  rfl

@[simp] theorem logKummerData_logKummer :
    logKummerData.logKummer = logKummer :=
  rfl

@[simp] theorem logKummerData_frobenius :
    logKummerData.frobenius = principalUnitFrobenius :=
  rfl

@[simp] theorem logKummerData_pScaling :
    logKummerData.pScaling = principalUnitLogShellFrobenius :=
  rfl

/-- The actual log-Kummer data is nonempty. -/
theorem logKummerData_nonempty : Nonempty LogKummerData :=
  ⟨logKummerData⟩

/-- The realified task-21 unit value kernel of the p-power Frobenius at the
concrete place is p times the realification. -/
theorem logKummerData_realification_frobenius
    (x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum) :
    (finitePlaceUnitValueKernel (F := GaussianField)
        concreteHeightOneSpectrum).realification (x ^ concreteRationalPrime) =
      (concreteRationalPrime : ℝ) *
        (finitePlaceUnitValueKernel (F := GaussianField)
          concreteHeightOneSpectrum).realification x :=
  concretePlace_unitValueKernel_realification_frobenius x

/-! ## 4. Inhabiting the non-source parts and freezing the source identification -/

/-- The scaled logarithm taking principal units to the actual integral
log-shell. -/
noncomputable def scaledPrincipalUnitLog
    (u : principalUnits (K := concreteLogShellField)) :
    integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :=
  ⟨((logShellScale concreteRationalPrime : concreteLogShellField)⁻¹) *
      unitLog (K := concreteLogShellField)
        (u : (Integers concreteLogShellField)ˣ),
    ⟨(u : (Integers concreteLogShellField)ˣ), rfl⟩⟩

/-- The p-fold scaling on the actual integral log-shell. -/
noncomputable def integralLogShellPScaling
    (x : integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)) :
    integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :=
  ⟨(concreteRationalPrime : concreteLogShellField) * (x : concreteLogShellField),
    integralLogShell_p_mul_mem x.2⟩

/-- The scaled logarithm commutes with the p-power Frobenius and the p-fold
scaling on the integral log-shell. -/
theorem scaledPrincipalUnitLog_frobenius
    (u : principalUnits (K := concreteLogShellField)) :
    scaledPrincipalUnitLog (principalUnitFrobenius u) =
      integralLogShellPScaling (scaledPrincipalUnitLog u) := by
  apply Subtype.ext
  change ((logShellScale concreteRationalPrime : concreteLogShellField)⁻¹) *
      unitLog (K := concreteLogShellField)
        (principalUnitFrobenius u : (Integers concreteLogShellField)ˣ) =
    (concreteRationalPrime : concreteLogShellField) *
      (((logShellScale concreteRationalPrime : concreteLogShellField)⁻¹) *
        unitLog (K := concreteLogShellField)
          (u : (Integers concreteLogShellField)ˣ))
  rw [unitLog_principalUnitFrobenius_log]
  ring

/-- The actual tree data populates the structural (non-source) fields of the
frozen source Frobenius/log-Kummer card: principal units, p-power Frobenius,
log-shell (the actual integral log-shell, where the p-fold scaling is proved
nontrivial), the scaled log-Kummer map, p-fold scaling, commutation and
nontriviality.  This is actual tree data, not an identification with the
source's Frobenius/log-Kummer operator. -/
noncomputable def treeSourceFrobeniusLogKummerCard (l : PrimeGeFive) :
    SourceFrobeniusLogKummerCard l where
  sourcePrincipalUnits := principalUnits (K := concreteLogShellField)
  sourceFrobenius := principalUnitFrobenius
  sourceLogShell :=
    integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
  logKummer := scaledPrincipalUnitLog
  pScaling := integralLogShellPScaling
  logKummer_frobenius := scaledPrincipalUnitLog_frobenius
  pScaling_nontrivial := by
    obtain ⟨x, hx, hne⟩ := integralLogShell_p_scaling_nontrivial
    refine ⟨⟨x, hx⟩, ?_⟩
    intro h
    exact hne (congrArg Subtype.val h)

/-- **Frozen card for the missing source identification of the actual
Frobenius/log-Kummer data.**  The non-source structural data is inhabited by
treeSourceFrobeniusLogKummerCard/logKummerData, but the identification of that
actual data with the source's Frobenius/log-Kummer operator is not constructed.
The card records the shape of the missing identification: source carriers and
maps together with equivalences intertwining them with the actual log-Kummer
data.  No inhabitant is constructed in this file and no theorem consumes one. -/
structure SourceFrobeniusLogKummerIdentificationCard (l : PrimeGeFive)
    (data : LogKummerData) where
  /-- The source principal-unit carrier. -/
  SourcePrincipalUnits : Type
  /-- The source Frobenius map. -/
  sourceFrobenius : SourcePrincipalUnits → SourcePrincipalUnits
  /-- The source log-shell carrier. -/
  SourceLogShell : Type
  /-- The source log-Kummer map. -/
  sourceLogKummer : SourcePrincipalUnits → SourceLogShell
  /-- The source p-fold scaling. -/
  sourcePScaling : SourceLogShell → SourceLogShell
  /-- Identification of the source principal-unit carrier with H. -/
  carrierEquiv : SourcePrincipalUnits ≃ data.H
  /-- Identification of the source log-shell with the tree log-shell. -/
  shellEquiv : SourceLogShell ≃ data.logShell
  /-- The source Frobenius intertwines with the tree Frobenius. -/
  frobenius_intertwines : ∀ h : SourcePrincipalUnits,
    carrierEquiv (sourceFrobenius h) = data.frobenius (carrierEquiv h)
  /-- The source log-Kummer map intertwines with the tree log-Kummer map. -/
  logKummer_intertwines : ∀ h : SourcePrincipalUnits,
    shellEquiv (sourceLogKummer h) = data.logKummer (carrierEquiv h)
  /-- The source p-fold scaling intertwines with the tree p-fold scaling. -/
  pScaling_intertwines : ∀ x : SourceLogShell,
    shellEquiv (sourcePScaling x) = data.pScaling (shellEquiv x)

/-! ## 5. Summary -/

/-- **Summary of the actual log-Kummer map.**  The map logKummer(x) = unitLog(x)
is additive on the actual principal units H, surjective onto the actual
principal-unit log-shell, with kernel exactly the torsion subgroup of H; it
commutes with the actual p-power Frobenius and the p-fold scaling on the shell;
the actual data is packaged as logKummerData; the non-source structural fields
of the source Frobenius/log-Kummer card are populated by actual tree data; the
source identification remains frozen as
SourceFrobeniusLogKummerIdentificationCard; and the realified p-power Frobenius
action on the task-21 unit value kernel is p times the realification. -/
theorem example36LogKummerMap_summary :
    Function.Surjective logKummer ∧
    (∀ u : principalUnits (K := concreteLogShellField),
      logKummer u = 0 ↔ IsOfFinOrder u) ∧
    ({u : principalUnits (K := concreteLogShellField) | logKummer u = 0} =
      (CommGroup.torsion (principalUnits (K := concreteLogShellField)) :
        Set (principalUnits (K := concreteLogShellField)))) ∧
    (∀ u : principalUnits (K := concreteLogShellField),
      logKummer (principalUnitFrobenius u) =
        principalUnitLogShellFrobenius (logKummer u)) ∧
    Nonempty LogKummerData ∧
    (∀ l : PrimeGeFive, Nonempty (SourceFrobeniusLogKummerCard l)) :=
  ⟨logKummer_surjective,
    logKummer_eq_zero_iff_isOfFinOrder,
    logKummer_kernel_eq_torsion,
    logKummer_commutes_frobenius,
    logKummerData_nonempty,
    fun l => ⟨treeSourceFrobeniusLogKummerCard l⟩⟩

end

end LogKummerMap
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the actual log-Kummer map from principal units to the
log-shell at the concrete Gaussian place.  The map logKummer = unitLog is
additive on the actual principal units H, surjective onto the principal-unit
log-shell, has kernel exactly the torsion subgroup of H, commutes with the
actual p-power Frobenius and p-fold scaling, is packaged as logKummerData; the
non-source structural fields of SourceFrobeniusLogKummerCard are inhabited by
actual tree data, while the source identification remains the frozen
SourceFrobeniusLogKummerIdentificationCard.  The realified p-power Frobenius
action is p times the realification.  No fake log-Kummer map or source
identification is claimed. -/
def example36LogKummerMap : Obligation :=
  { id := "IUT-II.example36-log-kummer-map"
    source :=
      "IUT III, Definition 1.1 and Remark 1.2.2 (log-shell and Frobenius " ++
        "action); IUT III, Proposition 1.2"
    status := VerificationStatus.interface
    note :=
      "Constructed the actual log-Kummer map at the concrete finite place: " ++
        "logKummer : H -> principalUnitLogShell, x |-> unitLog(x), from the " ++
        "actual principal units H of the concrete completion to the actual " ++
        "principal-unit log-shell (logKummer, logKummer_apply_coe).  It is " ++
        "additive on Additive H (logKummerAddHom, logKummerAddHom_apply), " ++
        "surjective onto the shell (logKummer_surjective: the shell is the " ++
        "image of unitLog on H), and its kernel is exactly the torsion locus " ++
        "(logKummer_eq_zero_iff_unitLog_eq_zero, " ++
        "logKummer_eq_zero_iff_isOfFinOrder, logKummer_kernel_eq_torsion, " ++
        "logKummerAddHom_ker).  Frobenius commutation: logKummer(x^p) = " ++
        "p * logKummer(x) (logKummer_commutes_frobenius, " ++
        "logKummer_frobenius_scaling), with the induced shell map exactly the " ++
        "p-fold scaling principalUnitLogShellFrobenius.  Packaged as " ++
        "LogKummerData with actual inhabitant logKummerData " ++
        "(logKummerData_nonempty).  Nontriviality/realification: the realified " ++
        "task-21 unit value kernel of the p-power Frobenius is p times the " ++
        "realification (logKummerData_realification_frobenius).  Inhabited the " ++
        "non-source structural fields of SourceFrobeniusLogKummerCard by actual " ++
        "tree data (treeSourceFrobeniusLogKummerCard; the log-shell there is " ++
        "the actual integral log-shell where the p-fold scaling is proved " ++
        "nontrivial).  The source identification of this data with the " ++
        "source's Frobenius/log-Kummer operator remains frozen as " ++
        "SourceFrobeniusLogKummerIdentificationCard with no inhabitant and no " ++
        "substitution.  No theta-pilot/q-pilot/Tate claim."
    dependsOn :=
      [ "IUT-II.example36-log-shell-lattice",
        "IUT-II.example36-log-shell-frobenius-action",
        "IUT-III.local-log-shell-frobenius-action",
        "IUT-III.log-shell-index-arithmetic" ] }

end LeanFormal.IUT.Audit
