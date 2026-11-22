$root='D:\lean'
$paths = Get-ChildItem -Directory (Join-Path $root '.lake\packages') | ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' } | Where-Object { Test-Path $_ }
$env:LEAN_PATH = ($paths -join ';') + ';' + (Join-Path $root '.lake\build\lib\lean')
$names = @('S3066ChartYOverlapPreimageActual','S3067PointRealizationActual','S3068GlobalReadoutLeActual','S3068OpenImmersionFactorizationActual','S3068PointRealizationClosed','S3071TorsorGroupoid','S3072QPrimePseudofunctor','S3076OneColumnMagnitudeProducerActual','S3078HullNativeMagnitudeProducerActual','S3079GlobalSumIdentificationAttempt','S3079PaperAlignmentQCoeffActual','S3080PaperConstantActual')
foreach ($n in $names) {
  $rel = 'tmp/sheaf/xif/paper/' + $n + '.lean'
  $src = Join-Path $root $rel
  if (-not (Test-Path $src)) { Write-Output ($n + ' NO_FILES'); continue }
  $ole = Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($rel,'olean'))
  & lake env lean -j1 -R $root -M 4096 -o $ole $src *> ('D:\lean\tmp\sheaf\xif\paper\' + $n + '.out') 2>&1
  Write-Output ($n + ' EXIT=' + $LASTEXITCODE + ' OLEAN=' + (Test-Path $ole))
}