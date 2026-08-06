import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks27

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 442368 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 443392 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 444416 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 445440 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 446464 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 447488 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 448512 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 449536 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 450560 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 451584 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 452608 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 453632 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 454656 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 455680 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 456704 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 457728 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 442368 ≤ i) (hi : i < 458752) : leafOK i = true := by
  have h0 := (shardOK_iff 442368 1024).mp chunk_00
  have h1 := (shardOK_iff 443392 1024).mp chunk_01
  have h2 := (shardOK_iff 444416 1024).mp chunk_02
  have h3 := (shardOK_iff 445440 1024).mp chunk_03
  have h4 := (shardOK_iff 446464 1024).mp chunk_04
  have h5 := (shardOK_iff 447488 1024).mp chunk_05
  have h6 := (shardOK_iff 448512 1024).mp chunk_06
  have h7 := (shardOK_iff 449536 1024).mp chunk_07
  have h8 := (shardOK_iff 450560 1024).mp chunk_08
  have h9 := (shardOK_iff 451584 1024).mp chunk_09
  have h10 := (shardOK_iff 452608 1024).mp chunk_10
  have h11 := (shardOK_iff 453632 1024).mp chunk_11
  have h12 := (shardOK_iff 454656 1024).mp chunk_12
  have h13 := (shardOK_iff 455680 1024).mp chunk_13
  have h14 := (shardOK_iff 456704 1024).mp chunk_14
  have h15 := (shardOK_iff 457728 1024).mp chunk_15
  by_cases e0 : i < 443392
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 444416
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 445440
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 446464
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 447488
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 448512
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 449536
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 450560
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 451584
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 452608
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 453632
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 454656
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 455680
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 456704
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 457728
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks27
