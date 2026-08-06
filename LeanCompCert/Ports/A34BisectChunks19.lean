import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks19

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 311296 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 312320 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 313344 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 314368 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 315392 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 316416 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 317440 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 318464 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 319488 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 320512 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 321536 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 322560 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 323584 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 324608 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 325632 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 326656 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 311296 ≤ i) (hi : i < 327680) : leafOK i = true := by
  have h0 := (shardOK_iff 311296 1024).mp chunk_00
  have h1 := (shardOK_iff 312320 1024).mp chunk_01
  have h2 := (shardOK_iff 313344 1024).mp chunk_02
  have h3 := (shardOK_iff 314368 1024).mp chunk_03
  have h4 := (shardOK_iff 315392 1024).mp chunk_04
  have h5 := (shardOK_iff 316416 1024).mp chunk_05
  have h6 := (shardOK_iff 317440 1024).mp chunk_06
  have h7 := (shardOK_iff 318464 1024).mp chunk_07
  have h8 := (shardOK_iff 319488 1024).mp chunk_08
  have h9 := (shardOK_iff 320512 1024).mp chunk_09
  have h10 := (shardOK_iff 321536 1024).mp chunk_10
  have h11 := (shardOK_iff 322560 1024).mp chunk_11
  have h12 := (shardOK_iff 323584 1024).mp chunk_12
  have h13 := (shardOK_iff 324608 1024).mp chunk_13
  have h14 := (shardOK_iff 325632 1024).mp chunk_14
  have h15 := (shardOK_iff 326656 1024).mp chunk_15
  by_cases e0 : i < 312320
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 313344
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 314368
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 315392
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 316416
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 317440
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 318464
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 319488
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 320512
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 321536
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 322560
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 323584
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 324608
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 325632
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 326656
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks19
