import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks17

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 278528 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 279552 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 280576 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 281600 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 282624 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 283648 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 284672 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 285696 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 286720 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 287744 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 288768 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 289792 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 290816 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 291840 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 292864 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 293888 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 278528 ≤ i) (hi : i < 294912) : leafOK i = true := by
  have h0 := (shardOK_iff 278528 1024).mp chunk_00
  have h1 := (shardOK_iff 279552 1024).mp chunk_01
  have h2 := (shardOK_iff 280576 1024).mp chunk_02
  have h3 := (shardOK_iff 281600 1024).mp chunk_03
  have h4 := (shardOK_iff 282624 1024).mp chunk_04
  have h5 := (shardOK_iff 283648 1024).mp chunk_05
  have h6 := (shardOK_iff 284672 1024).mp chunk_06
  have h7 := (shardOK_iff 285696 1024).mp chunk_07
  have h8 := (shardOK_iff 286720 1024).mp chunk_08
  have h9 := (shardOK_iff 287744 1024).mp chunk_09
  have h10 := (shardOK_iff 288768 1024).mp chunk_10
  have h11 := (shardOK_iff 289792 1024).mp chunk_11
  have h12 := (shardOK_iff 290816 1024).mp chunk_12
  have h13 := (shardOK_iff 291840 1024).mp chunk_13
  have h14 := (shardOK_iff 292864 1024).mp chunk_14
  have h15 := (shardOK_iff 293888 1024).mp chunk_15
  by_cases e0 : i < 279552
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 280576
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 281600
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 282624
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 283648
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 284672
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 285696
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 286720
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 287744
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 288768
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 289792
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 290816
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 291840
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 292864
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 293888
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks17
