import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks13

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 212992 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 214016 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 215040 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 216064 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 217088 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 218112 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 219136 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 220160 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 221184 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 222208 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 223232 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 224256 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 225280 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 226304 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 227328 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 228352 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 212992 ≤ i) (hi : i < 229376) : leafOK i = true := by
  have h0 := (shardOK_iff 212992 1024).mp chunk_00
  have h1 := (shardOK_iff 214016 1024).mp chunk_01
  have h2 := (shardOK_iff 215040 1024).mp chunk_02
  have h3 := (shardOK_iff 216064 1024).mp chunk_03
  have h4 := (shardOK_iff 217088 1024).mp chunk_04
  have h5 := (shardOK_iff 218112 1024).mp chunk_05
  have h6 := (shardOK_iff 219136 1024).mp chunk_06
  have h7 := (shardOK_iff 220160 1024).mp chunk_07
  have h8 := (shardOK_iff 221184 1024).mp chunk_08
  have h9 := (shardOK_iff 222208 1024).mp chunk_09
  have h10 := (shardOK_iff 223232 1024).mp chunk_10
  have h11 := (shardOK_iff 224256 1024).mp chunk_11
  have h12 := (shardOK_iff 225280 1024).mp chunk_12
  have h13 := (shardOK_iff 226304 1024).mp chunk_13
  have h14 := (shardOK_iff 227328 1024).mp chunk_14
  have h15 := (shardOK_iff 228352 1024).mp chunk_15
  by_cases e0 : i < 214016
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 215040
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 216064
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 217088
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 218112
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 219136
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 220160
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 221184
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 222208
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 223232
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 224256
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 225280
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 226304
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 227328
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 228352
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks13
