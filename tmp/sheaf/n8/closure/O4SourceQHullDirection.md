# O4 source Q <= Theta direction

## Actual production direction (reverse)
`sourceSignedHullLogVolume <= sourceSignedImageLogVolume` is proved from hull
containment (`sourceSignedHullLogVolume_le_sourceSignedImageLogVolume`).

## Needed direction
`sourceSignedImageLogVolume <= sourceSignedHullLogVolume`.

## Exact equivalence (proved)
Under finite hull volume, the needed signed direction is equivalent to the
via-images hull-volume identity

`sourceHullVolume v R n = sourceSetVolume v (possibleThetaPilotImageSet v R n)`.

The forward reduction uses `sourceHullVolume_eq_imageVolume_of_signedImageComparison`;
the converse uses `sourceSignedImageComparison_of_hullVolume_eq_imageVolume`.

## Decisive no-go
Production proves only the `>=` half of the volume identity
(`sourceSetVolume possibleImage <= sourceHullVolume`, from hull containment).
The missing `<=` half — hull volume at most possible-image volume — is not in
the tree.  Equivalently, the missing source theorem is the via-images
normalization: the hull is computed by the possible theta-pilot images.
No production lemma gives this equality, so the needed Q<=Theta source
direction is not derivable from current actual source data.
