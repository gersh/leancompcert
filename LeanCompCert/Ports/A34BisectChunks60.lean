import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks60

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 983040 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 984064 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 985088 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 986112 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 987136 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 988160 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 989184 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 990208 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 991232 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 992256 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 993280 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 994304 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 995328 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 996352 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 997376 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 998400 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 983040 ≤ i) (hi : i < 999424) : leafOK i = true := by
  have h0 := (shardOK_iff 983040 1024).mp chunk_00
  have h1 := (shardOK_iff 984064 1024).mp chunk_01
  have h2 := (shardOK_iff 985088 1024).mp chunk_02
  have h3 := (shardOK_iff 986112 1024).mp chunk_03
  have h4 := (shardOK_iff 987136 1024).mp chunk_04
  have h5 := (shardOK_iff 988160 1024).mp chunk_05
  have h6 := (shardOK_iff 989184 1024).mp chunk_06
  have h7 := (shardOK_iff 990208 1024).mp chunk_07
  have h8 := (shardOK_iff 991232 1024).mp chunk_08
  have h9 := (shardOK_iff 992256 1024).mp chunk_09
  have h10 := (shardOK_iff 993280 1024).mp chunk_10
  have h11 := (shardOK_iff 994304 1024).mp chunk_11
  have h12 := (shardOK_iff 995328 1024).mp chunk_12
  have h13 := (shardOK_iff 996352 1024).mp chunk_13
  have h14 := (shardOK_iff 997376 1024).mp chunk_14
  have h15 := (shardOK_iff 998400 1024).mp chunk_15
  by_cases e0 : i < 984064
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 985088
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 986112
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 987136
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 988160
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 989184
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 990208
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 991232
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 992256
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 993280
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 994304
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 995328
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 996352
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 997376
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 998400
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks60
