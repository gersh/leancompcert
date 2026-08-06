import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks20

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 327680 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 328704 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 329728 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 330752 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 331776 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 332800 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 333824 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 334848 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 335872 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 336896 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 337920 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 338944 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 339968 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 340992 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 342016 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 343040 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 327680 ≤ i) (hi : i < 344064) : leafOK i = true := by
  have h0 := (shardOK_iff 327680 1024).mp chunk_00
  have h1 := (shardOK_iff 328704 1024).mp chunk_01
  have h2 := (shardOK_iff 329728 1024).mp chunk_02
  have h3 := (shardOK_iff 330752 1024).mp chunk_03
  have h4 := (shardOK_iff 331776 1024).mp chunk_04
  have h5 := (shardOK_iff 332800 1024).mp chunk_05
  have h6 := (shardOK_iff 333824 1024).mp chunk_06
  have h7 := (shardOK_iff 334848 1024).mp chunk_07
  have h8 := (shardOK_iff 335872 1024).mp chunk_08
  have h9 := (shardOK_iff 336896 1024).mp chunk_09
  have h10 := (shardOK_iff 337920 1024).mp chunk_10
  have h11 := (shardOK_iff 338944 1024).mp chunk_11
  have h12 := (shardOK_iff 339968 1024).mp chunk_12
  have h13 := (shardOK_iff 340992 1024).mp chunk_13
  have h14 := (shardOK_iff 342016 1024).mp chunk_14
  have h15 := (shardOK_iff 343040 1024).mp chunk_15
  by_cases e0 : i < 328704
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 329728
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 330752
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 331776
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 332800
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 333824
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 334848
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 335872
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 336896
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 337920
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 338944
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 339968
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 340992
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 342016
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 343040
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks20
