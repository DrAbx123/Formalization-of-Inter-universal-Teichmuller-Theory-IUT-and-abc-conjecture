import tmp.sheaf.xif.paper.S3133QPilotReadoutActual
import tmp.sheaf.xif.paper.S3133QPilotBatchAInputActual

/-!
# q-pilot log-volume reading and Batch A Q_C source: module index

This module records where the q-pilot log-volume reading of the Batch A Q_C
source lives after the split into one-topic files:

* S3133QPilotReadoutActual: per-place readout of the actual Q_C source data
  (localSignedLog of the clause-B q_v), the paper log(q) = ord_v(q_v) log(p_v)
  form, the finite weighted global readout, and the identification of its
  procession-normalized value with the actual native q-pilot scalar -|log q|;
* S3133QPilotBatchAInputActual: the Batch A S3130QCLeHCData instantiated with
  the actual procession-normalized q-pilot log-volume as Q_C, independent of the
  ambient hull interface W.

No inequality is asserted; Q_C <= H_C remains the mainline S3130QCLeHCGap.
WRITE-ONLY.
-/
