@echo off
cd /d D:\lean
lake env lean tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.lean > "D:\lean\tmp\sheaf\xif\paper\S1413Compile.log" 2>&1
set RC=%ERRORLEVEL%
>> "D:\lean\tmp\sheaf\xif\paper\S1413Compile.log" echo EXIT=%RC%
