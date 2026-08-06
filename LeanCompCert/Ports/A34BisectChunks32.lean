import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks32

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 524288 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 525312 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 526336 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 527360 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 528384 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 529408 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 530432 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 531456 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 532480 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 533504 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 534528 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 535552 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 536576 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 537600 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 538624 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 539648 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 524288 ≤ i) (hi : i < 540672) : leafOK i = true := by
  have h0 := (shardOK_iff 524288 1024).mp chunk_00
  have h1 := (shardOK_iff 525312 1024).mp chunk_01
  have h2 := (shardOK_iff 526336 1024).mp chunk_02
  have h3 := (shardOK_iff 527360 1024).mp chunk_03
  have h4 := (shardOK_iff 528384 1024).mp chunk_04
  have h5 := (shardOK_iff 529408 1024).mp chunk_05
  have h6 := (shardOK_iff 530432 1024).mp chunk_06
  have h7 := (shardOK_iff 531456 1024).mp chunk_07
  have h8 := (shardOK_iff 532480 1024).mp chunk_08
  have h9 := (shardOK_iff 533504 1024).mp chunk_09
  have h10 := (shardOK_iff 534528 1024).mp chunk_10
  have h11 := (shardOK_iff 535552 1024).mp chunk_11
  have h12 := (shardOK_iff 536576 1024).mp chunk_12
  have h13 := (shardOK_iff 537600 1024).mp chunk_13
  have h14 := (shardOK_iff 538624 1024).mp chunk_14
  have h15 := (shardOK_iff 539648 1024).mp chunk_15
  by_cases e0 : i < 525312
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 526336
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 527360
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 528384
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 529408
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 530432
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 531456
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 532480
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 533504
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 534528
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 535552
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 536576
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 537600
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 538624
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 539648
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks32
