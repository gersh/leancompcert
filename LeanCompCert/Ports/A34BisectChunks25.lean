import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks25

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 409600 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 410624 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 411648 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 412672 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 413696 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 414720 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 415744 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 416768 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 417792 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 418816 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 419840 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 420864 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 421888 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 422912 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 423936 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 424960 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 409600 ≤ i) (hi : i < 425984) : leafOK i = true := by
  have h0 := (shardOK_iff 409600 1024).mp chunk_00
  have h1 := (shardOK_iff 410624 1024).mp chunk_01
  have h2 := (shardOK_iff 411648 1024).mp chunk_02
  have h3 := (shardOK_iff 412672 1024).mp chunk_03
  have h4 := (shardOK_iff 413696 1024).mp chunk_04
  have h5 := (shardOK_iff 414720 1024).mp chunk_05
  have h6 := (shardOK_iff 415744 1024).mp chunk_06
  have h7 := (shardOK_iff 416768 1024).mp chunk_07
  have h8 := (shardOK_iff 417792 1024).mp chunk_08
  have h9 := (shardOK_iff 418816 1024).mp chunk_09
  have h10 := (shardOK_iff 419840 1024).mp chunk_10
  have h11 := (shardOK_iff 420864 1024).mp chunk_11
  have h12 := (shardOK_iff 421888 1024).mp chunk_12
  have h13 := (shardOK_iff 422912 1024).mp chunk_13
  have h14 := (shardOK_iff 423936 1024).mp chunk_14
  have h15 := (shardOK_iff 424960 1024).mp chunk_15
  by_cases e0 : i < 410624
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 411648
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 412672
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 413696
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 414720
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 415744
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 416768
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 417792
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 418816
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 419840
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 420864
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 421888
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 422912
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 423936
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 424960
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks25
