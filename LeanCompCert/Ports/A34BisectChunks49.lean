import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks49

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 802816 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 803840 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 804864 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 805888 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 806912 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 807936 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 808960 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 809984 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 811008 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 812032 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 813056 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 814080 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 815104 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 816128 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 817152 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 818176 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 802816 ≤ i) (hi : i < 819200) : leafOK i = true := by
  have h0 := (shardOK_iff 802816 1024).mp chunk_00
  have h1 := (shardOK_iff 803840 1024).mp chunk_01
  have h2 := (shardOK_iff 804864 1024).mp chunk_02
  have h3 := (shardOK_iff 805888 1024).mp chunk_03
  have h4 := (shardOK_iff 806912 1024).mp chunk_04
  have h5 := (shardOK_iff 807936 1024).mp chunk_05
  have h6 := (shardOK_iff 808960 1024).mp chunk_06
  have h7 := (shardOK_iff 809984 1024).mp chunk_07
  have h8 := (shardOK_iff 811008 1024).mp chunk_08
  have h9 := (shardOK_iff 812032 1024).mp chunk_09
  have h10 := (shardOK_iff 813056 1024).mp chunk_10
  have h11 := (shardOK_iff 814080 1024).mp chunk_11
  have h12 := (shardOK_iff 815104 1024).mp chunk_12
  have h13 := (shardOK_iff 816128 1024).mp chunk_13
  have h14 := (shardOK_iff 817152 1024).mp chunk_14
  have h15 := (shardOK_iff 818176 1024).mp chunk_15
  by_cases e0 : i < 803840
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 804864
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 805888
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 806912
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 807936
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 808960
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 809984
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 811008
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 812032
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 813056
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 814080
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 815104
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 816128
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 817152
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 818176
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks49
