import tmp.sheaf.n8.closure.C1QuotientConsumerProbe
import tmp.sheaf.n8.closure.C1QuotientFiberData
import tmp.sheaf.n8.closure.C1PlaceValueGroupActual

/-!
# C1 old-strip Group from identification

From the missing old-strip identification

  C1OldStripMonIdentification I e:
    forall n m v, (I.primeStripAt n m).Mon v ≃* PlaceUnitMonoid F (e v)

the old fiber receives the canonical Group structure transported from
PlaceUnitMonoid along the equivalence (Equiv.group), and the actual place
kernel is pulled back along the transported MulEquiv.  This yields a literal
old-Mon quotient comparison, conditional on the identification.

The Group structure is not arbitrary: it is the transport of the actual place
unit group along the supplied monEquiv.  The identification itself remains the
single named gap.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1OldStripGroupFromIdentification

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.N8Closure.C1QuotientConsumerProbe
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui u

variable {l : PrimeGeFive}
variable {V : Type uv}

/-- Canonical Group structure on the old fiber: the existing monoid plus the
inverse transported from the actual place unit group.  The Monoid instance is
unchanged, so old-strip monoid equivalences continue to typecheck. -/
@[reducible] noncomputable def oldFiberGroup
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (D : C1OldStripMonIdentification I e)
    (n m : Int) (v : V) :
    Group ((I.primeStripAt n m).Mon v) := by
  let em := D.monEquiv n m v
  letI : Group ((I.primeStripAt n m).Mon v) :=
  { (inferInstance : Monoid ((I.primeStripAt n m).Mon v)) with
    inv := fun x => em.symm ((em x)⁻¹)
    inv_mul_cancel := by
      intro a
      apply em.injective
      simp [map_mul] }
  exact inferInstance

/-- Transported MulEquiv under the derived Group structure. -/
noncomputable def oldFiberMulEquiv
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (D : C1OldStripMonIdentification I e)
    (n m : Int) (v : V) :
    letI := oldFiberGroup I e D n m v
    ((I.primeStripAt n m).Mon v) ≃*
      PlaceUnitMonoid (F := I.initial.arithmetic.Fmod) (e v) := by
  letI := oldFiberGroup I e D n m v
  exact D.monEquiv n m v

/-- Transported kernel on the old fiber. -/
noncomputable def oldFiberKernel
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (D : C1OldStripMonIdentification I e)
    (n m : Int) (v : V) :
    letI := oldFiberGroup I e D n m v
    Subgroup ((I.primeStripAt n m).Mon v) := by
  letI := oldFiberGroup I e D n m v
  exact Subgroup.comap
    (D.monEquiv n m v).toMonoidHom
    (placeUnitKernel (F := I.initial.arithmetic.Fmod) (e v))

/-- Normality of the transported kernel: the old monoid is commutative. -/
theorem oldFiberKernelNormal
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (D : C1OldStripMonIdentification I e)
    (n m : Int) (v : V) :
    letI := oldFiberGroup I e D n m v
    (oldFiberKernel I e D n m v).Normal := by
  letI := oldFiberGroup I e D n m v
  letI : IsMulCommutative ((I.primeStripAt n m).Mon v) :=
    IsMulCommutative.of_comm (fun a b => mul_comm a b)
  exact Subgroup.normal_of_isMulCommutative _

/-- Literal old-Mon quotient comparison, conditional on the old-strip
identification and the actual quotient target. -/
noncomputable def oldFiberQuotientEquiv
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (D : C1OldStripMonIdentification I e)
    (Q : C1PlaceQuotientFiberData (F := I.initial.arithmetic.Fmod))
    (n m : Int) (v : V) :
    letI := oldFiberGroup I e D n m v
    letI := oldFiberKernelNormal I e D n m v
    ((I.primeStripAt n m).Mon v ⧸ oldFiberKernel I e D n m v) ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v) := by
  letI := oldFiberGroup I e D n m v
  letI := oldFiberKernelNormal I e D n m v
  let em := D.monEquiv n m v
  exact (QuotientGroup.congr
      (oldFiberKernel I e D n m v)
      (placeUnitKernel (F := I.initial.arithmetic.Fmod) (e v))
      em
      (Subgroup.map_comap_eq_self_of_surjective em.surjective
        (placeUnitKernel (F := I.initial.arithmetic.Fmod) (e v)))).trans
    (Q.quotientEquiv (e v))

/-- Structure carrying the derived old-Mon quotient consumer. -/
structure OldStripGroupQuotientConsumer
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (selected : V)
    (R : I.SourceImageRealization selected) where
  oldStripId : C1OldStripMonIdentification I e
  quotientData : C1PlaceQuotientFiberData (F := I.initial.arithmetic.Fmod)
  quotientFiber : ∀ (n m : Int) (v : V),
    letI := oldFiberGroup I e oldStripId n m v
    letI := oldFiberKernelNormal I e oldStripId n m v
    ((I.primeStripAt n m).Mon v ⧸ oldFiberKernel I e oldStripId n m v) ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)

/-- Construct the old-Mon quotient consumer from the old-strip identification
and the actual quotient target. -/
noncomputable def oldStripGroupQuotientConsumerOfIdent
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (selected : V) (R : I.SourceImageRealization selected)
    (D : C1OldStripMonIdentification I e) :
    OldStripGroupQuotientConsumer I e selected R where
  oldStripId := D
  quotientData := c1PlaceQuotientFiberData (F := I.initial.arithmetic.Fmod)
  quotientFiber := fun n m v =>
    oldFiberQuotientEquiv I e D
      (c1PlaceQuotientFiberData (F := I.initial.arithmetic.Fmod)) n m v

/-- Existence from the named old-strip gap.  The Group structure and kernel are
derived, not assumed arbitrarily. -/
theorem oldStripGroupQuotientConsumer_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (selected : V) (R : I.SourceImageRealization selected) :
    Nonempty (OldStripGroupQuotientConsumer I e selected R) := by
  obtain ⟨D⟩ := c1OldStripMonIdentification_nonempty I e
  exact ⟨oldStripGroupQuotientConsumerOfIdent I e selected R D⟩

end LeanFormal.IUT.N8Closure.C1OldStripGroupFromIdentification
