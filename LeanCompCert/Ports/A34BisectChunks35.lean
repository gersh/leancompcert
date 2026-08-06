import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks35

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 573440 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 574464 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 575488 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 576512 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 577536 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 578560 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 579584 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 580608 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 581632 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 582656 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 583680 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 584704 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 585728 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 586752 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 587776 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 588800 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 573440 ≤ i) (hi : i < 589824) : leafOK i = true := by
  have h0 := (shardOK_iff 573440 1024).mp chunk_00
  have h1 := (shardOK_iff 574464 1024).mp chunk_01
  have h2 := (shardOK_iff 575488 1024).mp chunk_02
  have h3 := (shardOK_iff 576512 1024).mp chunk_03
  have h4 := (shardOK_iff 577536 1024).mp chunk_04
  have h5 := (shardOK_iff 578560 1024).mp chunk_05
  have h6 := (shardOK_iff 579584 1024).mp chunk_06
  have h7 := (shardOK_iff 580608 1024).mp chunk_07
  have h8 := (shardOK_iff 581632 1024).mp chunk_08
  have h9 := (shardOK_iff 582656 1024).mp chunk_09
  have h10 := (shardOK_iff 583680 1024).mp chunk_10
  have h11 := (shardOK_iff 584704 1024).mp chunk_11
  have h12 := (shardOK_iff 585728 1024).mp chunk_12
  have h13 := (shardOK_iff 586752 1024).mp chunk_13
  have h14 := (shardOK_iff 587776 1024).mp chunk_14
  have h15 := (shardOK_iff 588800 1024).mp chunk_15
  by_cases e0 : i < 574464
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 575488
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 576512
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 577536
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 578560
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 579584
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 580608
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 581632
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 582656
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 583680
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 584704
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 585728
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 586752
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 587776
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 588800
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks35
