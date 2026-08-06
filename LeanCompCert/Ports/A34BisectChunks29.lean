import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks29

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 475136 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 476160 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 477184 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 478208 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 479232 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 480256 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 481280 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 482304 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 483328 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 484352 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 485376 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 486400 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 487424 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 488448 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 489472 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 490496 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 475136 ≤ i) (hi : i < 491520) : leafOK i = true := by
  have h0 := (shardOK_iff 475136 1024).mp chunk_00
  have h1 := (shardOK_iff 476160 1024).mp chunk_01
  have h2 := (shardOK_iff 477184 1024).mp chunk_02
  have h3 := (shardOK_iff 478208 1024).mp chunk_03
  have h4 := (shardOK_iff 479232 1024).mp chunk_04
  have h5 := (shardOK_iff 480256 1024).mp chunk_05
  have h6 := (shardOK_iff 481280 1024).mp chunk_06
  have h7 := (shardOK_iff 482304 1024).mp chunk_07
  have h8 := (shardOK_iff 483328 1024).mp chunk_08
  have h9 := (shardOK_iff 484352 1024).mp chunk_09
  have h10 := (shardOK_iff 485376 1024).mp chunk_10
  have h11 := (shardOK_iff 486400 1024).mp chunk_11
  have h12 := (shardOK_iff 487424 1024).mp chunk_12
  have h13 := (shardOK_iff 488448 1024).mp chunk_13
  have h14 := (shardOK_iff 489472 1024).mp chunk_14
  have h15 := (shardOK_iff 490496 1024).mp chunk_15
  by_cases e0 : i < 476160
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 477184
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 478208
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 479232
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 480256
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 481280
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 482304
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 483328
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 484352
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 485376
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 486400
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 487424
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 488448
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 489472
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 490496
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks29
