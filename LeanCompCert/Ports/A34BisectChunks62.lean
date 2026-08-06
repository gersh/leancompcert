import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks62

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 1015808 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 1016832 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 1017856 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 1018880 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 1019904 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 1020928 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 1021952 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 1022976 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 1024000 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 1025024 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 1026048 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 1027072 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 1028096 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 1029120 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 1030144 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 1031168 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 1015808 ≤ i) (hi : i < 1032192) : leafOK i = true := by
  have h0 := (shardOK_iff 1015808 1024).mp chunk_00
  have h1 := (shardOK_iff 1016832 1024).mp chunk_01
  have h2 := (shardOK_iff 1017856 1024).mp chunk_02
  have h3 := (shardOK_iff 1018880 1024).mp chunk_03
  have h4 := (shardOK_iff 1019904 1024).mp chunk_04
  have h5 := (shardOK_iff 1020928 1024).mp chunk_05
  have h6 := (shardOK_iff 1021952 1024).mp chunk_06
  have h7 := (shardOK_iff 1022976 1024).mp chunk_07
  have h8 := (shardOK_iff 1024000 1024).mp chunk_08
  have h9 := (shardOK_iff 1025024 1024).mp chunk_09
  have h10 := (shardOK_iff 1026048 1024).mp chunk_10
  have h11 := (shardOK_iff 1027072 1024).mp chunk_11
  have h12 := (shardOK_iff 1028096 1024).mp chunk_12
  have h13 := (shardOK_iff 1029120 1024).mp chunk_13
  have h14 := (shardOK_iff 1030144 1024).mp chunk_14
  have h15 := (shardOK_iff 1031168 1024).mp chunk_15
  by_cases e0 : i < 1016832
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 1017856
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 1018880
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 1019904
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 1020928
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 1021952
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 1022976
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 1024000
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 1025024
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 1026048
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 1027072
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 1028096
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 1029120
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 1030144
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 1031168
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks62
