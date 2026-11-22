import tmp.sheaf.xif.paper.S3136BDClassChainToolActual

/-! # Stage-4 host: IUT IV Corollary 2.2, (i) BD-class chain composition instance

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt,
Corollary 2.2, (i) (p.2404-2428; proof p.2506-2529): the equality of BD-classes
  (1/6) log(q-non2(-)) ~ (1/6) log(q-forall(-)) ~ (1/6) ht_inf ~ ht_omega_X(D)
on K_V, proved from [GenEll] Proposition 1.4, (i), (iii) and the degree-6
computation (all class A).

CONSUMER: mainline's Cor 2.2 (i) statement slot. This file instantiates the
generic BD-class chain tool on four abstract functions: it shows that the exact
Cor 2.2 (i) chain is a composition of four BD-class relations, so the only
remaining analytic inputs are the individual relations (each recorded as data).

LABEL: class A composition instance. Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136Cor22BDChainInstanceActual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual

variable {α : Type*} (F : Set α)
variable (f1 f2 f3 f4 : α → ℝ)

/-- The Cor 2.2 (i) chain data: the four BD-class relations of the display. -/
structure LGPCor22ChainData where
  h12 : IsBDLe f1 f2 F
  h23 : IsBDLe f2 f3 F
  h34 : IsBDLe f3 f4 F

/-- The composite BD-class relation of the Cor 2.2 (i) chain: the first and last
functions differ by a bounded constant. -/
theorem LGPCor22ChainData.composite (D : LGPCor22ChainData F f1 f2 f3 f4) :
    IsBDLe f1 f4 F :=
  isBDLe_trans (isBDLe_trans D.h12 D.h23) D.h34

/-- The chain data also gives the reverse composite for the last and first. -/
theorem LGPCor22ChainData.composite' (D : LGPCor22ChainData F f1 f2 f3 f4)
    (h21 : IsBDLe f2 f1 F) (h32 : IsBDLe f3 f2 F) (h43 : IsBDLe f4 f3 F) :
    IsBDEq f1 f4 F :=
  ⟨D.composite, isBDLe_trans (isBDLe_trans h43 h32) h21⟩

#check LGPCor22ChainData
#check LGPCor22ChainData.composite
#check LGPCor22ChainData.composite'

end LeanFormal.IUT.XiFPaper.S3136Cor22BDChainInstanceActual