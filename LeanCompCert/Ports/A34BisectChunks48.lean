import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks48

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 786432 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 787456 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 788480 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 789504 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 790528 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 791552 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 792576 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 793600 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 794624 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 795648 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 796672 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 797696 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 798720 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 799744 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 800768 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 801792 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 786432 ≤ i) (hi : i < 802816) : leafOK i = true := by
  have h0 := (shardOK_iff 786432 1024).mp chunk_00
  have h1 := (shardOK_iff 787456 1024).mp chunk_01
  have h2 := (shardOK_iff 788480 1024).mp chunk_02
  have h3 := (shardOK_iff 789504 1024).mp chunk_03
  have h4 := (shardOK_iff 790528 1024).mp chunk_04
  have h5 := (shardOK_iff 791552 1024).mp chunk_05
  have h6 := (shardOK_iff 792576 1024).mp chunk_06
  have h7 := (shardOK_iff 793600 1024).mp chunk_07
  have h8 := (shardOK_iff 794624 1024).mp chunk_08
  have h9 := (shardOK_iff 795648 1024).mp chunk_09
  have h10 := (shardOK_iff 796672 1024).mp chunk_10
  have h11 := (shardOK_iff 797696 1024).mp chunk_11
  have h12 := (shardOK_iff 798720 1024).mp chunk_12
  have h13 := (shardOK_iff 799744 1024).mp chunk_13
  have h14 := (shardOK_iff 800768 1024).mp chunk_14
  have h15 := (shardOK_iff 801792 1024).mp chunk_15
  by_cases e0 : i < 787456
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 788480
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 789504
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 790528
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 791552
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 792576
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 793600
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 794624
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 795648
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 796672
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 797696
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 798720
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 799744
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 800768
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 801792
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks48
