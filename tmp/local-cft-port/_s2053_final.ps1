$ErrorActionPreference = 'Continue'
$log = 'D:\lean\tmp\local-cft-port\_s2053_final.tsv'
$raw = 'D:\lean\tmp\local-cft-port\_s2053_final.raw.log'
$TAB = [char]9
$pkgs = 'D:\lean\.lake\packages'
$env:LEAN_PATH = @(
  "$pkgs\Cli\.lake\build\lib\lean", "$pkgs\batteries\.lake\build\lib\lean", "$pkgs\Qq\.lake\build\lib\lean", "$pkgs\aesop\.lake\build\lib\lean", "$pkgs\proofwidgets\.lake\build\lib\lean", "$pkgs\importGraph\.lake\build\lib\lean", "$pkgs\LeanSearchClient\.lake\build\lib\lean", "$pkgs\plausible\.lake\build\lib\lean", "$pkgs\mathlib\.lake\build\lib\lean", 'D:\lean\.lake\build\lib\lean'
) -join ';'
$PROOT = 'D:/lean/tmp/local-cft-port'
$OUTDIR = 'D:\lean\.lake\build\lib\lean'
$opts = @('-D','pp.unicode.fun=true','-D','relaxedAutoImplicit=false','-D','weak.linter.mathlibStandardSet=true','-D','maxSynthPendingDepth=3')
$mods = @(@('PadicField.ZHat','PadicField/ZHat.lean'),@('PadicField.PowIndex','PadicField/PowIndex.lean'),@('PadicField.PowIndexPadic','PadicField/PowIndexPadic.lean'))
"START $(Get-Date -Format o)" | Set-Content $raw
foreach ($t in $mods) {
  $m = $t[0]; $rel = $t[1]
  $src = "$PROOT/$rel"
  $outFile = Join-Path $OUTDIR ($rel.Replace('/','\') -replace '\.lean$','.olean')
  $srchash = (Get-FileHash $src -Algorithm SHA256).Hash
  $done = $false
  for ($i = 1; $i -le 5; $i++) {
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $o = (& lean -j1 @opts -R $PROOT -o $outFile $src 2>&1 | Out-String)
    $code = $LASTEXITCODE
    $sw.Stop()
    $sec = [math]::Round($sw.Elapsed.TotalSeconds,1)
    ("ATTEMPT $m try=$i exit=$code sec=$sec") | Add-Content $raw
    if ($code -eq 0) {
      $done = $true
      $b2 = (Get-Item $outFile).Length
      $oh = (Get-FileHash $outFile -Algorithm SHA256).Hash
      (@($m,'EXIT=0',"SEC=$sec","OLEAN_BYTES=$b2","OLEAN_SHA256=$oh","SRC_SHA256=$srchash") -join $TAB) | Add-Content $log
      break
    }
    if ($o.Trim().Length -gt 0) { ("----- OUTPUT $m try=$i -----") | Add-Content $raw; $o | Add-Content $raw }
    if ($o -match 'failed to read file|cannot open|could not read|object file .* does not exist|failed to create file|Stack overflow') {
      ("TRANSIENT $m try=$i; sleeping") | Add-Content $raw
      Start-Sleep -Seconds 10
    } else { break }
  }
  if (-not $done) { (@($m,'EXIT=FAIL',"SRC_SHA256=$srchash") -join $TAB) | Add-Content $log; ("HARDSTOP $m") | Add-Content $raw; break }
}
"ALLDONE $(Get-Date -Format o)" | Add-Content $raw