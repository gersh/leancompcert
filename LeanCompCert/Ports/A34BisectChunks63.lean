import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks63

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 1032192 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 1033216 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 1034240 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 1035264 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 1036288 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 1037312 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 1038336 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 1039360 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 1040384 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 1041408 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 1042432 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 1043456 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 1044480 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 1045504 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 1046528 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 1047552 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 1032192 ≤ i) (hi : i < 1048576) : leafOK i = true := by
  have h0 := (shardOK_iff 1032192 1024).mp chunk_00
  have h1 := (shardOK_iff 1033216 1024).mp chunk_01
  have h2 := (shardOK_iff 1034240 1024).mp chunk_02
  have h3 := (shardOK_iff 1035264 1024).mp chunk_03
  have h4 := (shardOK_iff 1036288 1024).mp chunk_04
  have h5 := (shardOK_iff 1037312 1024).mp chunk_05
  have h6 := (shardOK_iff 1038336 1024).mp chunk_06
  have h7 := (shardOK_iff 1039360 1024).mp chunk_07
  have h8 := (shardOK_iff 1040384 1024).mp chunk_08
  have h9 := (shardOK_iff 1041408 1024).mp chunk_09
  have h10 := (shardOK_iff 1042432 1024).mp chunk_10
  have h11 := (shardOK_iff 1043456 1024).mp chunk_11
  have h12 := (shardOK_iff 1044480 1024).mp chunk_12
  have h13 := (shardOK_iff 1045504 1024).mp chunk_13
  have h14 := (shardOK_iff 1046528 1024).mp chunk_14
  have h15 := (shardOK_iff 1047552 1024).mp chunk_15
  by_cases e0 : i < 1033216
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 1034240
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 1035264
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 1036288
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 1037312
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 1038336
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 1039360
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 1040384
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 1041408
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 1042432
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 1043456
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 1044480
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 1045504
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 1046528
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 1047552
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks63
