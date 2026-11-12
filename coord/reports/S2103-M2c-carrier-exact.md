# S2103: LocalArtinSourceData from M2a + exact M2c carrier gap

Date: 2026-11-02. Layer O; consumer S2027/S2024.

## Actual

S2102 gives M2a-torsion:

  S2046M2TorsionRequired_actual U :
    mu p U ≃* CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)).

S2103 constructs, for any carrier comparison hC:

  localArtinSourceDataOfCarrier hC : LocalArtinSourceData p
    with artin := S2046M2TorsionRequired_actual
         carrier := hC.

Lean:

  tmp/sheaf/xif/paper/S2103LocalArtinSourceDataM2c.lean
  source SHA256 920A604F412C6C22AF15CF755771C73733BFC2A2D0853E0A6A6C28C02B50ACA1
  EXIT=0
  olean SHA256 7CB698F66026595A1847DD88F78490D26E6E85FE7596CD11B2C4ECD451A17DBC
  size 30144
  axioms propext, Classical.choice, Quot.sound.

## Exact missing M2c

  CarrierComparison U :
    CommGroup.torsion (Abelianization ↥U) ≃*
      CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)).

Equivalently S2027 profiniteTorsionComparison U.  S2027 has only
abelianizationToTopological_surjective; injectivity on torsion is not in the
tree.

## M2b

After M2c, S2027 localReciprocityData_of_source needs transfer compatibility;
S2098 records it as localReciprocityTransferCompatibility.  Brauer.ArtinTransfer
port is separate.

## Conclusion

- BUILT: conditional LocalArtinSourceData from M2c; M2a actual from S2102.
- MISSING: M2c carrier comparison.
- no fake; no inhabitant of M2c assumed.
