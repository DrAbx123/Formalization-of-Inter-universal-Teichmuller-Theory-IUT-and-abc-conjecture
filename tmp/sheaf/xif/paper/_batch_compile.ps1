$root='D:\lean'
$paths = Get-ChildItem -Directory (Join-Path $root '.lake\packages') | ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' } | Where-Object { Test-Path $_ }
$env:LEAN_PATH = ($paths -join ';') + ';' + (Join-Path $root '.lake\build\lib\lean')
$names = @('S2795PlaceAbsNormLeSqActual','S2796SupportAbsNormLeRadSqActual','S2800LineBundleCor312BridgeActual','S2813ClauseA37ReadyActual','S2813SG3aHullDeterminantTransportActual','S2814BadPlaceContractActual','S2814ClauseBParameterActual','S2814SG3bLocalPacketActual','S2811IsPrestackActual','S2811PActual','S2811P2Actual','S2811P3Actual','S2811P4Actual')
foreach ($n in $names) {
  $rel = 'tmp/sheaf/xif/paper/' + $n + '.lean'
  $src = Join-Path $root $rel
  $ole = Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($rel,'olean'))
  & lake env lean -j1 -R $root -M 4096 -o $ole $src *> ('D:\lean\tmp\sheaf\xif\paper\' + $n + '.out') 2>&1
  $ex = $LASTEXITCODE
  $oe = Test-Path $ole
  Write-Output ($n + ' EXIT=' + $ex + ' OLEAN=' + $oe)
}