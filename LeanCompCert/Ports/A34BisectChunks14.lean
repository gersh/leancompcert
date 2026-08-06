import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks14

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 229376 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 230400 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 231424 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 232448 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 233472 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 234496 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 235520 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 236544 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 237568 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 238592 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 239616 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 240640 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 241664 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 242688 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 243712 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 244736 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 229376 ≤ i) (hi : i < 245760) : leafOK i = true := by
  have h0 := (shardOK_iff 229376 1024).mp chunk_00
  have h1 := (shardOK_iff 230400 1024).mp chunk_01
  have h2 := (shardOK_iff 231424 1024).mp chunk_02
  have h3 := (shardOK_iff 232448 1024).mp chunk_03
  have h4 := (shardOK_iff 233472 1024).mp chunk_04
  have h5 := (shardOK_iff 234496 1024).mp chunk_05
  have h6 := (shardOK_iff 235520 1024).mp chunk_06
  have h7 := (shardOK_iff 236544 1024).mp chunk_07
  have h8 := (shardOK_iff 237568 1024).mp chunk_08
  have h9 := (shardOK_iff 238592 1024).mp chunk_09
  have h10 := (shardOK_iff 239616 1024).mp chunk_10
  have h11 := (shardOK_iff 240640 1024).mp chunk_11
  have h12 := (shardOK_iff 241664 1024).mp chunk_12
  have h13 := (shardOK_iff 242688 1024).mp chunk_13
  have h14 := (shardOK_iff 243712 1024).mp chunk_14
  have h15 := (shardOK_iff 244736 1024).mp chunk_15
  by_cases e0 : i < 230400
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 231424
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 232448
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 233472
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 234496
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 235520
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 236544
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 237568
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 238592
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 239616
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 240640
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 241664
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 242688
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 243712
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 244736
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks14
