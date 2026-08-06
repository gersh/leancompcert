import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks23

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 376832 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 377856 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 378880 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 379904 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 380928 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 381952 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 382976 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 384000 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 385024 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 386048 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 387072 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 388096 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 389120 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 390144 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 391168 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 392192 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 376832 ≤ i) (hi : i < 393216) : leafOK i = true := by
  have h0 := (shardOK_iff 376832 1024).mp chunk_00
  have h1 := (shardOK_iff 377856 1024).mp chunk_01
  have h2 := (shardOK_iff 378880 1024).mp chunk_02
  have h3 := (shardOK_iff 379904 1024).mp chunk_03
  have h4 := (shardOK_iff 380928 1024).mp chunk_04
  have h5 := (shardOK_iff 381952 1024).mp chunk_05
  have h6 := (shardOK_iff 382976 1024).mp chunk_06
  have h7 := (shardOK_iff 384000 1024).mp chunk_07
  have h8 := (shardOK_iff 385024 1024).mp chunk_08
  have h9 := (shardOK_iff 386048 1024).mp chunk_09
  have h10 := (shardOK_iff 387072 1024).mp chunk_10
  have h11 := (shardOK_iff 388096 1024).mp chunk_11
  have h12 := (shardOK_iff 389120 1024).mp chunk_12
  have h13 := (shardOK_iff 390144 1024).mp chunk_13
  have h14 := (shardOK_iff 391168 1024).mp chunk_14
  have h15 := (shardOK_iff 392192 1024).mp chunk_15
  by_cases e0 : i < 377856
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 378880
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 379904
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 380928
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 381952
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 382976
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 384000
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 385024
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 386048
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 387072
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 388096
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 389120
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 390144
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 391168
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 392192
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks23
