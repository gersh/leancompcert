import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks24

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 393216 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 394240 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 395264 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 396288 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 397312 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 398336 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 399360 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 400384 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 401408 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 402432 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 403456 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 404480 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 405504 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 406528 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 407552 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 408576 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 393216 ≤ i) (hi : i < 409600) : leafOK i = true := by
  have h0 := (shardOK_iff 393216 1024).mp chunk_00
  have h1 := (shardOK_iff 394240 1024).mp chunk_01
  have h2 := (shardOK_iff 395264 1024).mp chunk_02
  have h3 := (shardOK_iff 396288 1024).mp chunk_03
  have h4 := (shardOK_iff 397312 1024).mp chunk_04
  have h5 := (shardOK_iff 398336 1024).mp chunk_05
  have h6 := (shardOK_iff 399360 1024).mp chunk_06
  have h7 := (shardOK_iff 400384 1024).mp chunk_07
  have h8 := (shardOK_iff 401408 1024).mp chunk_08
  have h9 := (shardOK_iff 402432 1024).mp chunk_09
  have h10 := (shardOK_iff 403456 1024).mp chunk_10
  have h11 := (shardOK_iff 404480 1024).mp chunk_11
  have h12 := (shardOK_iff 405504 1024).mp chunk_12
  have h13 := (shardOK_iff 406528 1024).mp chunk_13
  have h14 := (shardOK_iff 407552 1024).mp chunk_14
  have h15 := (shardOK_iff 408576 1024).mp chunk_15
  by_cases e0 : i < 394240
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 395264
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 396288
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 397312
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 398336
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 399360
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 400384
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 401408
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 402432
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 403456
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 404480
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 405504
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 406528
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 407552
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 408576
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks24
