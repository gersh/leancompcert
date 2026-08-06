import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks01

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 16384 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 17408 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 18432 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 19456 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 20480 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 21504 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 22528 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 23552 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 24576 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 25600 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 26624 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 27648 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 28672 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 29696 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 30720 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 31744 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 16384 ≤ i) (hi : i < 32768) : leafOK i = true := by
  have h0 := (shardOK_iff 16384 1024).mp chunk_00
  have h1 := (shardOK_iff 17408 1024).mp chunk_01
  have h2 := (shardOK_iff 18432 1024).mp chunk_02
  have h3 := (shardOK_iff 19456 1024).mp chunk_03
  have h4 := (shardOK_iff 20480 1024).mp chunk_04
  have h5 := (shardOK_iff 21504 1024).mp chunk_05
  have h6 := (shardOK_iff 22528 1024).mp chunk_06
  have h7 := (shardOK_iff 23552 1024).mp chunk_07
  have h8 := (shardOK_iff 24576 1024).mp chunk_08
  have h9 := (shardOK_iff 25600 1024).mp chunk_09
  have h10 := (shardOK_iff 26624 1024).mp chunk_10
  have h11 := (shardOK_iff 27648 1024).mp chunk_11
  have h12 := (shardOK_iff 28672 1024).mp chunk_12
  have h13 := (shardOK_iff 29696 1024).mp chunk_13
  have h14 := (shardOK_iff 30720 1024).mp chunk_14
  have h15 := (shardOK_iff 31744 1024).mp chunk_15
  by_cases e0 : i < 17408
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 18432
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 19456
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 20480
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 21504
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 22528
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 23552
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 24576
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 25600
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 26624
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 27648
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 28672
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 29696
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 30720
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 31744
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks01
