import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks16

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 262144 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 263168 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 264192 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 265216 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 266240 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 267264 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 268288 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 269312 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 270336 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 271360 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 272384 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 273408 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 274432 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 275456 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 276480 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 277504 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 262144 ≤ i) (hi : i < 278528) : leafOK i = true := by
  have h0 := (shardOK_iff 262144 1024).mp chunk_00
  have h1 := (shardOK_iff 263168 1024).mp chunk_01
  have h2 := (shardOK_iff 264192 1024).mp chunk_02
  have h3 := (shardOK_iff 265216 1024).mp chunk_03
  have h4 := (shardOK_iff 266240 1024).mp chunk_04
  have h5 := (shardOK_iff 267264 1024).mp chunk_05
  have h6 := (shardOK_iff 268288 1024).mp chunk_06
  have h7 := (shardOK_iff 269312 1024).mp chunk_07
  have h8 := (shardOK_iff 270336 1024).mp chunk_08
  have h9 := (shardOK_iff 271360 1024).mp chunk_09
  have h10 := (shardOK_iff 272384 1024).mp chunk_10
  have h11 := (shardOK_iff 273408 1024).mp chunk_11
  have h12 := (shardOK_iff 274432 1024).mp chunk_12
  have h13 := (shardOK_iff 275456 1024).mp chunk_13
  have h14 := (shardOK_iff 276480 1024).mp chunk_14
  have h15 := (shardOK_iff 277504 1024).mp chunk_15
  by_cases e0 : i < 263168
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 264192
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 265216
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 266240
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 267264
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 268288
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 269312
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 270336
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 271360
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 272384
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 273408
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 274432
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 275456
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 276480
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 277504
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks16
