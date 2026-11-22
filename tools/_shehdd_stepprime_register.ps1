$f='coord/target-chain.mainline.json'  # node may be defined elsewhere; search all fragments
$j = $null
$files = @('dag/target-chain.json') + (Get-ChildItem coord -Filter 'target-chain.*.json' | Where-Object { $_.Name -ne 'target-chain.TEMPLATE.json' } | ForEach-Object { 'coord/' + $_.Name })
foreach ($path in $files) {
  $tmp = Get-Content $path -Raw | ConvertFrom-Json
  $node = $tmp.nodes | Where-Object { $_.id -eq 'B4c-c-stepprovider' }
  if ($node) {
    $node.declarations = @{ 'tmp/sheaf/xif/paper/Mzk1StepProviderPrimeActual.lean' = @('exists_maxDegP_finite','stepSetP1','mem_stepSetP1_of_mem','mem_stepSetP1_of_conj','mem_stepSetP1_of_crit','degQ_le_of_mem_conjSet','maxDegP_stepSetP1_le','F4NumMaxStrictInput','measure_stepSetP1_lt_of_named','StepProvider''','StepProviderFixedBetaChoiceInput','F0StepTransportInput','stepProvider'_of_inputs') }
    $node.note = 'A424 restated beta-f0; f1/f2/f4a PROVED in file; f4b (F4NumMaxStrictInput) + f5 (F0StepTransportInput) NAMED; assembly stepProvider''_of_inputs PROVED conditional; fixed-beta equivalence named; repaired 4 compile errors (monic.ne_zero, membership defeq, calc <=, rows length 10) — watchdog recompile pending.'
    $tmp | ConvertTo-Json -Depth 10 | Set-Content $path -Encoding utf8
    Write-Output ('updated ' + $path)
  }
}
