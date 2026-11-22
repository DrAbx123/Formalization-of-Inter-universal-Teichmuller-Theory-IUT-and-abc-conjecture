
$names = @('T_aesop','T_fieldsimp_lin','T_fieldsimp_ring','T_gcongr','T_grind','T_linarith','T_nlinarith','T_normnum','T_omega','T_positivity','T_ringnf','T_simp')
$res = $names | ForEach-Object -Parallel {
  $name = $_
  $lean = 'D:\lean\tmp\sheaf\xif\paper\_taskK\' + $name + '.lean'
  $log  = 'D:\lean\tmp\sheaf\xif\paper\_taskK\out\' + $name + '.log'
  Set-Location 'D:\lean'
  & lake env lean $lean *> $log
  [pscustomobject]@{ Name=$name; Exit=$LASTEXITCODE; Bytes=(Get-Item $log).Length }
} -ThrottleLimit 6
$res | Sort-Object Name | Format-Table -AutoSize | Out-String -Width 120
