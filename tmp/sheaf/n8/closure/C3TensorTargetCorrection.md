# Wave18: C3 tensor target correction

Date: 2026-10-24
Owner: kummer
Files: C3TensorTargetCorrection.lean, this md
Status: actual over-F tensor block/insertion + exact frozen-target gap

## Correction

Frozen C3 tensor target (NativeTensorLandingDonor) uses:

  tensorPlaces : (i) -> V i -> FinitePlaceAtPrime Fmod p

i.e. a finitePadicTensor of Fmod-completion factors.

Actual native q lives in the F-completion at nativeFPlaceOverBad.

The correct tensor base for the native q is therefore over F, not Fmod.

## Actual construction in the Lean file

- nativePrime := completionRationalPrime(nativeFPlaceOverBad)
- nativeFPlaceAtPrime : FinitePlaceAtPrime F nativePrime
- overFTensorBlock :=
    FinitePadicTensor (fun _ : PUnit =>
      CommonPrimeCompletion nativeFPlaceAtPrime)
- overFTensorInsertion :
    Completion nativeFPlaceOverBad -> overFTensorBlock
    via finitePadicTensorTprod, with the definitional cast
    Completion nativeFPlaceOverBad = CommonPrimeCompletion nativeFPlaceAtPrime
- nativeQOverFTensor (D) := overFTensorInsertion (nativeQUnit X D)

## Decisive gap

The frozen NativeTensorLandingDonor target is a different block (Fmod factors),
not the over-F block above.  No production comparison Fmod-tensor <-> over-F
tensor exists, so the frozen target cannot be identified with the over-F
construction.  The single named sorry is

nativeTensorLandingDonor_frozen_target_nonempty.

No arbitrary linear map, free tuple, or free comparison is introduced.
