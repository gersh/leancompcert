import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks50

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 819200 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 820224 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 821248 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 822272 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 823296 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 824320 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 825344 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 826368 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 827392 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 828416 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 829440 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 830464 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 831488 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 832512 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 833536 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 834560 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 819200 ≤ i) (hi : i < 835584) : leafOK i = true := by
  have h0 := (shardOK_iff 819200 1024).mp chunk_00
  have h1 := (shardOK_iff 820224 1024).mp chunk_01
  have h2 := (shardOK_iff 821248 1024).mp chunk_02
  have h3 := (shardOK_iff 822272 1024).mp chunk_03
  have h4 := (shardOK_iff 823296 1024).mp chunk_04
  have h5 := (shardOK_iff 824320 1024).mp chunk_05
  have h6 := (shardOK_iff 825344 1024).mp chunk_06
  have h7 := (shardOK_iff 826368 1024).mp chunk_07
  have h8 := (shardOK_iff 827392 1024).mp chunk_08
  have h9 := (shardOK_iff 828416 1024).mp chunk_09
  have h10 := (shardOK_iff 829440 1024).mp chunk_10
  have h11 := (shardOK_iff 830464 1024).mp chunk_11
  have h12 := (shardOK_iff 831488 1024).mp chunk_12
  have h13 := (shardOK_iff 832512 1024).mp chunk_13
  have h14 := (shardOK_iff 833536 1024).mp chunk_14
  have h15 := (shardOK_iff 834560 1024).mp chunk_15
  by_cases e0 : i < 820224
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 821248
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 822272
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 823296
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 824320
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 825344
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 826368
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 827392
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 828416
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 829440
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 830464
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 831488
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 832512
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 833536
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 834560
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks50
