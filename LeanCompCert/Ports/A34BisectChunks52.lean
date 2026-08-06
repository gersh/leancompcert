import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks52

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 851968 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 852992 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 854016 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 855040 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 856064 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 857088 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 858112 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 859136 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 860160 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 861184 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 862208 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 863232 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 864256 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 865280 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 866304 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 867328 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 851968 ≤ i) (hi : i < 868352) : leafOK i = true := by
  have h0 := (shardOK_iff 851968 1024).mp chunk_00
  have h1 := (shardOK_iff 852992 1024).mp chunk_01
  have h2 := (shardOK_iff 854016 1024).mp chunk_02
  have h3 := (shardOK_iff 855040 1024).mp chunk_03
  have h4 := (shardOK_iff 856064 1024).mp chunk_04
  have h5 := (shardOK_iff 857088 1024).mp chunk_05
  have h6 := (shardOK_iff 858112 1024).mp chunk_06
  have h7 := (shardOK_iff 859136 1024).mp chunk_07
  have h8 := (shardOK_iff 860160 1024).mp chunk_08
  have h9 := (shardOK_iff 861184 1024).mp chunk_09
  have h10 := (shardOK_iff 862208 1024).mp chunk_10
  have h11 := (shardOK_iff 863232 1024).mp chunk_11
  have h12 := (shardOK_iff 864256 1024).mp chunk_12
  have h13 := (shardOK_iff 865280 1024).mp chunk_13
  have h14 := (shardOK_iff 866304 1024).mp chunk_14
  have h15 := (shardOK_iff 867328 1024).mp chunk_15
  by_cases e0 : i < 852992
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 854016
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 855040
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 856064
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 857088
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 858112
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 859136
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 860160
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 861184
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 862208
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 863232
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 864256
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 865280
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 866304
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 867328
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks52
