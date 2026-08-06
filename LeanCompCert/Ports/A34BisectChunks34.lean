import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks34

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 557056 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 558080 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 559104 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 560128 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 561152 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 562176 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 563200 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 564224 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 565248 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 566272 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 567296 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 568320 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 569344 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 570368 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 571392 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 572416 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 557056 ≤ i) (hi : i < 573440) : leafOK i = true := by
  have h0 := (shardOK_iff 557056 1024).mp chunk_00
  have h1 := (shardOK_iff 558080 1024).mp chunk_01
  have h2 := (shardOK_iff 559104 1024).mp chunk_02
  have h3 := (shardOK_iff 560128 1024).mp chunk_03
  have h4 := (shardOK_iff 561152 1024).mp chunk_04
  have h5 := (shardOK_iff 562176 1024).mp chunk_05
  have h6 := (shardOK_iff 563200 1024).mp chunk_06
  have h7 := (shardOK_iff 564224 1024).mp chunk_07
  have h8 := (shardOK_iff 565248 1024).mp chunk_08
  have h9 := (shardOK_iff 566272 1024).mp chunk_09
  have h10 := (shardOK_iff 567296 1024).mp chunk_10
  have h11 := (shardOK_iff 568320 1024).mp chunk_11
  have h12 := (shardOK_iff 569344 1024).mp chunk_12
  have h13 := (shardOK_iff 570368 1024).mp chunk_13
  have h14 := (shardOK_iff 571392 1024).mp chunk_14
  have h15 := (shardOK_iff 572416 1024).mp chunk_15
  by_cases e0 : i < 558080
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 559104
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 560128
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 561152
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 562176
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 563200
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 564224
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 565248
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 566272
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 567296
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 568320
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 569344
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 570368
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 571392
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 572416
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks34
