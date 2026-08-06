import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks28

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 458752 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 459776 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 460800 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 461824 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 462848 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 463872 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 464896 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 465920 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 466944 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 467968 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 468992 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 470016 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 471040 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 472064 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 473088 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 474112 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 458752 ≤ i) (hi : i < 475136) : leafOK i = true := by
  have h0 := (shardOK_iff 458752 1024).mp chunk_00
  have h1 := (shardOK_iff 459776 1024).mp chunk_01
  have h2 := (shardOK_iff 460800 1024).mp chunk_02
  have h3 := (shardOK_iff 461824 1024).mp chunk_03
  have h4 := (shardOK_iff 462848 1024).mp chunk_04
  have h5 := (shardOK_iff 463872 1024).mp chunk_05
  have h6 := (shardOK_iff 464896 1024).mp chunk_06
  have h7 := (shardOK_iff 465920 1024).mp chunk_07
  have h8 := (shardOK_iff 466944 1024).mp chunk_08
  have h9 := (shardOK_iff 467968 1024).mp chunk_09
  have h10 := (shardOK_iff 468992 1024).mp chunk_10
  have h11 := (shardOK_iff 470016 1024).mp chunk_11
  have h12 := (shardOK_iff 471040 1024).mp chunk_12
  have h13 := (shardOK_iff 472064 1024).mp chunk_13
  have h14 := (shardOK_iff 473088 1024).mp chunk_14
  have h15 := (shardOK_iff 474112 1024).mp chunk_15
  by_cases e0 : i < 459776
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 460800
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 461824
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 462848
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 463872
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 464896
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 465920
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 466944
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 467968
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 468992
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 470016
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 471040
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 472064
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 473088
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 474112
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks28
