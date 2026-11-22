$ErrorActionPreference='SilentlyContinue'
$root='D:/lean'
$seedsFile=Join-Path $root 'dag/watchdog/extra-targets.txt'
$topoFile=Join-Path $root 'tmp/external/ported/lana_core/topo_order.txt'
$portRoot='tmp/external/ported/lana_core'
$prefix='tmp.external.ported.lana_core.'
function Olean([string]$p){ $o=Join-Path $root ('.lake/build/lib/lean/' + ($p -replace '\.lean$','') + '.olean'); return (Test-Path $o) }
function Imports([string]$p){ $abs=Join-Path $root $p; if(-not (Test-Path $abs)){ return @() }; $ls=Get-Content $abs | Where-Object { $_ -match '^\s*import ' }; $out=@(); foreach($l in $ls){ $m=[regex]::Match($l,'^\s*import\s+(\S+)'); if(-not $m.Success){continue}; $mod=$m.Groups[1].Value; if($mod.StartsWith($prefix)){ $out += ($portRoot + '/' + (($mod.Substring($prefix.Length)) -replace '\.','/') + '.lean') } elseif($mod -eq 'PadicLogVolume.PadicLog'){ $out += 'PadicLogVolume/PadicLog.lean' } elseif($mod -eq 'PadicLogVolume.TraceDuality'){ $out += 'PadicLogVolume/TraceDuality.lean' } }; return $out }
$budget=240; $i=0
while($i -lt $budget){
  $files=Get-Content $topoFile | Where-Object { $_ -match 'lana_core' }
  $seeds=Get-Content $seedsFile | Where-Object { $_ }
  $added=0
  foreach($f in $files){ if(Olean $f){ continue }; $imps=Imports $f; $ok=$true; foreach($d in $imps){ if($d -like "$portRoot/*" -and -not (Olean $d)){ $ok=$false; break } }; if($ok -and -not ($seeds -contains $f)){ $seeds += $f; [IO.File]::WriteAllText($seedsFile, (($seeds -join "`r`n") + "`r`n"), (New-Object System.Text.UTF8Encoding($false))); $added++; break } }
  $allDone=$true; foreach($f in $files){ if(-not (Olean $f)){ $allDone=$false; break } }
  if($allDone){ Write-Output 'FEEDER DONE all oleans'; break }
  Start-Sleep -Seconds 15; $i++
}
$c=0; foreach($f in $files){ if(Olean $f){ $c++ } }; Write-Output ('FEEDER EXIT i=' + $i + ' oleans=' + $c + '/' + $files.Count)