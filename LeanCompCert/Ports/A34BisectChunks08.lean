import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks08

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 131072 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 132096 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 133120 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 134144 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 135168 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 136192 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 137216 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 138240 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 139264 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 140288 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 141312 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 142336 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 143360 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 144384 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 145408 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 146432 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 131072 ≤ i) (hi : i < 147456) : leafOK i = true := by
  have h0 := (shardOK_iff 131072 1024).mp chunk_00
  have h1 := (shardOK_iff 132096 1024).mp chunk_01
  have h2 := (shardOK_iff 133120 1024).mp chunk_02
  have h3 := (shardOK_iff 134144 1024).mp chunk_03
  have h4 := (shardOK_iff 135168 1024).mp chunk_04
  have h5 := (shardOK_iff 136192 1024).mp chunk_05
  have h6 := (shardOK_iff 137216 1024).mp chunk_06
  have h7 := (shardOK_iff 138240 1024).mp chunk_07
  have h8 := (shardOK_iff 139264 1024).mp chunk_08
  have h9 := (shardOK_iff 140288 1024).mp chunk_09
  have h10 := (shardOK_iff 141312 1024).mp chunk_10
  have h11 := (shardOK_iff 142336 1024).mp chunk_11
  have h12 := (shardOK_iff 143360 1024).mp chunk_12
  have h13 := (shardOK_iff 144384 1024).mp chunk_13
  have h14 := (shardOK_iff 145408 1024).mp chunk_14
  have h15 := (shardOK_iff 146432 1024).mp chunk_15
  by_cases e0 : i < 132096
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 133120
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 134144
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 135168
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 136192
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 137216
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 138240
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 139264
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 140288
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 141312
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 142336
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 143360
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 144384
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 145408
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 146432
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks08
