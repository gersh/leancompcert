import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks26

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 425984 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 427008 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 428032 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 429056 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 430080 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 431104 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 432128 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 433152 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 434176 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 435200 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 436224 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 437248 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 438272 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 439296 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 440320 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 441344 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 425984 ≤ i) (hi : i < 442368) : leafOK i = true := by
  have h0 := (shardOK_iff 425984 1024).mp chunk_00
  have h1 := (shardOK_iff 427008 1024).mp chunk_01
  have h2 := (shardOK_iff 428032 1024).mp chunk_02
  have h3 := (shardOK_iff 429056 1024).mp chunk_03
  have h4 := (shardOK_iff 430080 1024).mp chunk_04
  have h5 := (shardOK_iff 431104 1024).mp chunk_05
  have h6 := (shardOK_iff 432128 1024).mp chunk_06
  have h7 := (shardOK_iff 433152 1024).mp chunk_07
  have h8 := (shardOK_iff 434176 1024).mp chunk_08
  have h9 := (shardOK_iff 435200 1024).mp chunk_09
  have h10 := (shardOK_iff 436224 1024).mp chunk_10
  have h11 := (shardOK_iff 437248 1024).mp chunk_11
  have h12 := (shardOK_iff 438272 1024).mp chunk_12
  have h13 := (shardOK_iff 439296 1024).mp chunk_13
  have h14 := (shardOK_iff 440320 1024).mp chunk_14
  have h15 := (shardOK_iff 441344 1024).mp chunk_15
  by_cases e0 : i < 427008
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 428032
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 429056
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 430080
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 431104
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 432128
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 433152
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 434176
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 435200
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 436224
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 437248
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 438272
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 439296
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 440320
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 441344
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks26
