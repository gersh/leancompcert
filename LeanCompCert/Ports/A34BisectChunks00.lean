import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks00

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 0 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 1024 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 2048 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 3072 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 4096 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 5120 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 6144 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 7168 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 8192 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 9216 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 10240 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 11264 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 12288 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 13312 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 14336 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 15360 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hi : i < 16384) : leafOK i = true := by
  have h0 := (shardOK_iff 0 1024).mp chunk_00
  have h1 := (shardOK_iff 1024 1024).mp chunk_01
  have h2 := (shardOK_iff 2048 1024).mp chunk_02
  have h3 := (shardOK_iff 3072 1024).mp chunk_03
  have h4 := (shardOK_iff 4096 1024).mp chunk_04
  have h5 := (shardOK_iff 5120 1024).mp chunk_05
  have h6 := (shardOK_iff 6144 1024).mp chunk_06
  have h7 := (shardOK_iff 7168 1024).mp chunk_07
  have h8 := (shardOK_iff 8192 1024).mp chunk_08
  have h9 := (shardOK_iff 9216 1024).mp chunk_09
  have h10 := (shardOK_iff 10240 1024).mp chunk_10
  have h11 := (shardOK_iff 11264 1024).mp chunk_11
  have h12 := (shardOK_iff 12288 1024).mp chunk_12
  have h13 := (shardOK_iff 13312 1024).mp chunk_13
  have h14 := (shardOK_iff 14336 1024).mp chunk_14
  have h15 := (shardOK_iff 15360 1024).mp chunk_15
  by_cases e0 : i < 1024
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 2048
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 3072
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 4096
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 5120
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 6144
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 7168
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 8192
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 9216
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 10240
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 11264
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 12288
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 13312
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 14336
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 15360
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks00
