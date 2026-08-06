import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks44

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 720896 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 721920 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 722944 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 723968 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 724992 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 726016 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 727040 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 728064 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 729088 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 730112 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 731136 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 732160 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 733184 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 734208 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 735232 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 736256 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 720896 ≤ i) (hi : i < 737280) : leafOK i = true := by
  have h0 := (shardOK_iff 720896 1024).mp chunk_00
  have h1 := (shardOK_iff 721920 1024).mp chunk_01
  have h2 := (shardOK_iff 722944 1024).mp chunk_02
  have h3 := (shardOK_iff 723968 1024).mp chunk_03
  have h4 := (shardOK_iff 724992 1024).mp chunk_04
  have h5 := (shardOK_iff 726016 1024).mp chunk_05
  have h6 := (shardOK_iff 727040 1024).mp chunk_06
  have h7 := (shardOK_iff 728064 1024).mp chunk_07
  have h8 := (shardOK_iff 729088 1024).mp chunk_08
  have h9 := (shardOK_iff 730112 1024).mp chunk_09
  have h10 := (shardOK_iff 731136 1024).mp chunk_10
  have h11 := (shardOK_iff 732160 1024).mp chunk_11
  have h12 := (shardOK_iff 733184 1024).mp chunk_12
  have h13 := (shardOK_iff 734208 1024).mp chunk_13
  have h14 := (shardOK_iff 735232 1024).mp chunk_14
  have h15 := (shardOK_iff 736256 1024).mp chunk_15
  by_cases e0 : i < 721920
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 722944
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 723968
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 724992
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 726016
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 727040
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 728064
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 729088
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 730112
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 731136
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 732160
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 733184
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 734208
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 735232
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 736256
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks44
