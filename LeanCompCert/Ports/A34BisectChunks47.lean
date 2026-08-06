import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks47

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 770048 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 771072 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 772096 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 773120 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 774144 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 775168 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 776192 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 777216 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 778240 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 779264 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 780288 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 781312 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 782336 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 783360 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 784384 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 785408 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 770048 ≤ i) (hi : i < 786432) : leafOK i = true := by
  have h0 := (shardOK_iff 770048 1024).mp chunk_00
  have h1 := (shardOK_iff 771072 1024).mp chunk_01
  have h2 := (shardOK_iff 772096 1024).mp chunk_02
  have h3 := (shardOK_iff 773120 1024).mp chunk_03
  have h4 := (shardOK_iff 774144 1024).mp chunk_04
  have h5 := (shardOK_iff 775168 1024).mp chunk_05
  have h6 := (shardOK_iff 776192 1024).mp chunk_06
  have h7 := (shardOK_iff 777216 1024).mp chunk_07
  have h8 := (shardOK_iff 778240 1024).mp chunk_08
  have h9 := (shardOK_iff 779264 1024).mp chunk_09
  have h10 := (shardOK_iff 780288 1024).mp chunk_10
  have h11 := (shardOK_iff 781312 1024).mp chunk_11
  have h12 := (shardOK_iff 782336 1024).mp chunk_12
  have h13 := (shardOK_iff 783360 1024).mp chunk_13
  have h14 := (shardOK_iff 784384 1024).mp chunk_14
  have h15 := (shardOK_iff 785408 1024).mp chunk_15
  by_cases e0 : i < 771072
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 772096
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 773120
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 774144
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 775168
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 776192
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 777216
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 778240
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 779264
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 780288
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 781312
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 782336
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 783360
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 784384
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 785408
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks47
