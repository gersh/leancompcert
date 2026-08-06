import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks40

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 655360 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 656384 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 657408 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 658432 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 659456 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 660480 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 661504 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 662528 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 663552 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 664576 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 665600 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 666624 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 667648 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 668672 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 669696 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 670720 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 655360 ≤ i) (hi : i < 671744) : leafOK i = true := by
  have h0 := (shardOK_iff 655360 1024).mp chunk_00
  have h1 := (shardOK_iff 656384 1024).mp chunk_01
  have h2 := (shardOK_iff 657408 1024).mp chunk_02
  have h3 := (shardOK_iff 658432 1024).mp chunk_03
  have h4 := (shardOK_iff 659456 1024).mp chunk_04
  have h5 := (shardOK_iff 660480 1024).mp chunk_05
  have h6 := (shardOK_iff 661504 1024).mp chunk_06
  have h7 := (shardOK_iff 662528 1024).mp chunk_07
  have h8 := (shardOK_iff 663552 1024).mp chunk_08
  have h9 := (shardOK_iff 664576 1024).mp chunk_09
  have h10 := (shardOK_iff 665600 1024).mp chunk_10
  have h11 := (shardOK_iff 666624 1024).mp chunk_11
  have h12 := (shardOK_iff 667648 1024).mp chunk_12
  have h13 := (shardOK_iff 668672 1024).mp chunk_13
  have h14 := (shardOK_iff 669696 1024).mp chunk_14
  have h15 := (shardOK_iff 670720 1024).mp chunk_15
  by_cases e0 : i < 656384
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 657408
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 658432
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 659456
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 660480
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 661504
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 662528
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 663552
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 664576
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 665600
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 666624
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 667648
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 668672
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 669696
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 670720
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks40
