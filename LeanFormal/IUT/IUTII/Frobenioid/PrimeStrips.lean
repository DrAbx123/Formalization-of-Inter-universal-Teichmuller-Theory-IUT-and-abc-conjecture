import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def frobenioidPrimeStrips : Obligation :=
  { id := "IUT-I-II.prime-strips-frobenioids"
    source := "IUT I, Sections 5-6; Geometry of Frobenioids I-II"
    status := VerificationStatus.interface
    note :=
      "Construct the prime strips and Frobenioid links from lower-layer objects; the carrier and degree kernels are proved separately. Interface-level reduction pass done: " ++
        "carriers and fiber links in `PrimeStripsConstruction.lean` (kernel `IUT-II.prime-strip-construction-kernel`), the degree kernel in `PrimeStripDegree.lean`, and the Frobenioid link layer in `PrimeStripsFrobenioidLinks.lean` (`IUT-II.prime-strips-frobenioid-link-layer`, status interface): the contract `PrimeStripFrobenioidLinkLayer` " ++
        "(degree/transport block of the frozen `K2FrobenioidBoundary`, realification derived) is assembled conditionally from `ModDirectionCard` (inhabited by the finite-place model) and `MODDirectionCard`. Still open: card CAT " ++
        "(categorical `Cv`, `C⊢v`, `C⊩mod`; direct construction blocked at the sharpness of divisorial monoids), the general MOD direction, and boundary items (1), (2), (4) of `IUT-II.prime-strips-frobenioid-boundary`." ++
        "Rounds: `PrimeStripFrobenioidCards.lean` " ++
        "(`IUT-II.prime-strips-frobenioid-card-reductions`) and " ++
        "`PrimeStripFrobenioidSkeletonCards.lean` " ++
        "(`IUT-II.prime-strips-frobenioid-skeleton-cards`)."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core",
        "IUT-I-II.prime-strip-degree-kernel",
        "IUT-I-II.local-prime-place-carrier",
        "IUT-I-II.local-f-prime-strip-carrier" ] }

end LeanFormal.IUT.Audit
