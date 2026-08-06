import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks21

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 344064 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 345088 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 346112 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 347136 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 348160 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 349184 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 350208 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 351232 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 352256 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 353280 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 354304 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 355328 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 356352 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 357376 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 358400 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 359424 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 344064 ≤ i) (hi : i < 360448) : leafOK i = true := by
  have h0 := (shardOK_iff 344064 1024).mp chunk_00
  have h1 := (shardOK_iff 345088 1024).mp chunk_01
  have h2 := (shardOK_iff 346112 1024).mp chunk_02
  have h3 := (shardOK_iff 347136 1024).mp chunk_03
  have h4 := (shardOK_iff 348160 1024).mp chunk_04
  have h5 := (shardOK_iff 349184 1024).mp chunk_05
  have h6 := (shardOK_iff 350208 1024).mp chunk_06
  have h7 := (shardOK_iff 351232 1024).mp chunk_07
  have h8 := (shardOK_iff 352256 1024).mp chunk_08
  have h9 := (shardOK_iff 353280 1024).mp chunk_09
  have h10 := (shardOK_iff 354304 1024).mp chunk_10
  have h11 := (shardOK_iff 355328 1024).mp chunk_11
  have h12 := (shardOK_iff 356352 1024).mp chunk_12
  have h13 := (shardOK_iff 357376 1024).mp chunk_13
  have h14 := (shardOK_iff 358400 1024).mp chunk_14
  have h15 := (shardOK_iff 359424 1024).mp chunk_15
  by_cases e0 : i < 345088
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 346112
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 347136
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 348160
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 349184
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 350208
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 351232
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 352256
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 353280
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 354304
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 355328
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 356352
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 357376
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 358400
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 359424
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks21
