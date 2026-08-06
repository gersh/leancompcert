import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks05

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 81920 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 82944 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 83968 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 84992 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 86016 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 87040 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 88064 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 89088 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 90112 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 91136 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 92160 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 93184 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 94208 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 95232 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 96256 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 97280 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 81920 ≤ i) (hi : i < 98304) : leafOK i = true := by
  have h0 := (shardOK_iff 81920 1024).mp chunk_00
  have h1 := (shardOK_iff 82944 1024).mp chunk_01
  have h2 := (shardOK_iff 83968 1024).mp chunk_02
  have h3 := (shardOK_iff 84992 1024).mp chunk_03
  have h4 := (shardOK_iff 86016 1024).mp chunk_04
  have h5 := (shardOK_iff 87040 1024).mp chunk_05
  have h6 := (shardOK_iff 88064 1024).mp chunk_06
  have h7 := (shardOK_iff 89088 1024).mp chunk_07
  have h8 := (shardOK_iff 90112 1024).mp chunk_08
  have h9 := (shardOK_iff 91136 1024).mp chunk_09
  have h10 := (shardOK_iff 92160 1024).mp chunk_10
  have h11 := (shardOK_iff 93184 1024).mp chunk_11
  have h12 := (shardOK_iff 94208 1024).mp chunk_12
  have h13 := (shardOK_iff 95232 1024).mp chunk_13
  have h14 := (shardOK_iff 96256 1024).mp chunk_14
  have h15 := (shardOK_iff 97280 1024).mp chunk_15
  by_cases e0 : i < 82944
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 83968
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 84992
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 86016
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 87040
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 88064
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 89088
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 90112
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 91136
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 92160
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 93184
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 94208
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 95232
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 96256
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 97280
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks05
