import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks31

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 507904 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 508928 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 509952 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 510976 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 512000 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 513024 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 514048 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 515072 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 516096 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 517120 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 518144 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 519168 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 520192 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 521216 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 522240 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 523264 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 507904 ≤ i) (hi : i < 524288) : leafOK i = true := by
  have h0 := (shardOK_iff 507904 1024).mp chunk_00
  have h1 := (shardOK_iff 508928 1024).mp chunk_01
  have h2 := (shardOK_iff 509952 1024).mp chunk_02
  have h3 := (shardOK_iff 510976 1024).mp chunk_03
  have h4 := (shardOK_iff 512000 1024).mp chunk_04
  have h5 := (shardOK_iff 513024 1024).mp chunk_05
  have h6 := (shardOK_iff 514048 1024).mp chunk_06
  have h7 := (shardOK_iff 515072 1024).mp chunk_07
  have h8 := (shardOK_iff 516096 1024).mp chunk_08
  have h9 := (shardOK_iff 517120 1024).mp chunk_09
  have h10 := (shardOK_iff 518144 1024).mp chunk_10
  have h11 := (shardOK_iff 519168 1024).mp chunk_11
  have h12 := (shardOK_iff 520192 1024).mp chunk_12
  have h13 := (shardOK_iff 521216 1024).mp chunk_13
  have h14 := (shardOK_iff 522240 1024).mp chunk_14
  have h15 := (shardOK_iff 523264 1024).mp chunk_15
  by_cases e0 : i < 508928
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 509952
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 510976
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 512000
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 513024
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 514048
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 515072
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 516096
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 517120
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 518144
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 519168
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 520192
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 521216
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 522240
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 523264
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks31
