import Mathlib

/-!
# Mzk1PrimeStripsValueKernelV2Actual — value kernels of additive homs (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Kernel of an additive homomorphism is an additive subgroup (closure proofs fixed). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsValueKernelV2Actual

/-- Kernel set of an additive homomorphism. -/
def kernelSet {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) : Set G :=
  { x | f x = 0 }

/-- Genuine theorem: zero lies in the kernel. -/
theorem zero_mem_kernelSet {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) :
    (0 : G) ∈ kernelSet f :=
  map_zero f

/-- Genuine theorem: kernel is closed under addition. -/
theorem add_mem_kernelSet {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    {a b : G} (ha : a ∈ kernelSet f) (hb : b ∈ kernelSet f) : a + b ∈ kernelSet f := by
  change f (a + b) = 0
  change f a = 0 at ha
  change f b = 0 at hb
  rw [map_add, ha, hb, add_zero]

/-- Genuine theorem: kernel is closed under negation. -/
theorem neg_mem_kernelSet {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    {a : G} (ha : a ∈ kernelSet f) : -a ∈ kernelSet f := by
  change f (-a) = 0
  change f a = 0 at ha
  rw [map_neg, ha, neg_zero]

/-- The value kernel as an additive subgroup. -/
def valueKernel {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) : AddSubgroup G where
  carrier := kernelSet f
  zero_mem' := zero_mem_kernelSet f
  add_mem' := fun ha hb => add_mem_kernelSet f ha hb
  neg_mem' := fun ha => neg_mem_kernelSet f ha

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsValueKernelV2Actual
