import tmp.sheaf.xif.paper.S2564Chain1Mid2Actual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Verify

/- Type acceptance: the lemmas have exactly the requested statement. -/
example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 81 = (G * S0).coeff 81 := chain1_coeff_81
example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 100 = (G * S0).coeff 100 := chain1_coeff_100
example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 120 = (G * S0).coeff 120 := chain1_coeff_120
example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 160 = (G * S0).coeff 160 := chain1_coeff_160
example : ∀ n : ℕ, 81 ≤ n → n ≤ 160 → ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n :=
  chain1_coeff_mid2
example : S0.coeff 69 = 240 := S0_coeff_69
example : S0.coeff 80 = 590 := S0_coeff_80
example : S0.coeff 81 = 240 := S0_coeff_81
example : S0.coeff 160 = 363 := S0_coeff_160

/- Axiom audit for every declaration in the new module. -/

#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.R0_coeff_eq_zero_of_gt
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.R1_coeff_eq_zero_of_gt
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_69
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_70
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_71
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_72
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_73
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_74
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_75
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_76
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_77
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_78
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_79
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_80
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_81
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_82
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_83
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_84
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_85
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_86
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_87
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_88
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_89
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_90
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_91
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_92
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_93
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_94
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_95
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_96
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_97
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_98
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_99
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_100
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_101
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_102
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_103
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_104
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_105
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_106
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_107
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_108
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_109
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_110
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_111
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_112
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_113
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_114
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_115
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_116
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_117
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_118
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_119
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_120
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_121
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_122
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_123
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_124
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_125
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_126
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_127
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_128
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_129
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_130
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_131
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_132
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_133
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_134
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_135
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_136
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_137
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_138
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_139
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_140
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_141
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_142
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_143
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_144
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_145
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_146
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_147
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_148
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_149
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_150
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_151
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_152
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_153
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_154
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_155
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_156
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_157
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_158
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_159
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.S0_coeff_160
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_81
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_82
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_83
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_84
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_85
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_86
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_87
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_88
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_89
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_90
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_91
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_92
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_93
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_94
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_95
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_96
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_97
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_98
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_99
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_100
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_101
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_102
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_103
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_104
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_105
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_106
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_107
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_108
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_109
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_110
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_111
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_112
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_113
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_114
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_115
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_116
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_117
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_118
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_119
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_120
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_121
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_122
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_123
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_124
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_125
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_126
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_127
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_128
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_129
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_130
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_131
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_132
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_133
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_134
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_135
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_136
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_137
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_138
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_139
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_140
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_141
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_142
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_143
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_144
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_145
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_146
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_147
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_148
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_149
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_150
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_151
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_152
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_153
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_154
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_155
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_156
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_157
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_158
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_159
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_160
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_mid2

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Verify
