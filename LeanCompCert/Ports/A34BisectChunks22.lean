import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks22

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 360448 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 361472 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 362496 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 363520 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 364544 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 365568 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 366592 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 367616 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 368640 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 369664 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 370688 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 371712 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 372736 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 373760 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 374784 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 375808 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 360448 ≤ i) (hi : i < 376832) : leafOK i = true := by
  have h0 := (shardOK_iff 360448 1024).mp chunk_00
  have h1 := (shardOK_iff 361472 1024).mp chunk_01
  have h2 := (shardOK_iff 362496 1024).mp chunk_02
  have h3 := (shardOK_iff 363520 1024).mp chunk_03
  have h4 := (shardOK_iff 364544 1024).mp chunk_04
  have h5 := (shardOK_iff 365568 1024).mp chunk_05
  have h6 := (shardOK_iff 366592 1024).mp chunk_06
  have h7 := (shardOK_iff 367616 1024).mp chunk_07
  have h8 := (shardOK_iff 368640 1024).mp chunk_08
  have h9 := (shardOK_iff 369664 1024).mp chunk_09
  have h10 := (shardOK_iff 370688 1024).mp chunk_10
  have h11 := (shardOK_iff 371712 1024).mp chunk_11
  have h12 := (shardOK_iff 372736 1024).mp chunk_12
  have h13 := (shardOK_iff 373760 1024).mp chunk_13
  have h14 := (shardOK_iff 374784 1024).mp chunk_14
  have h15 := (shardOK_iff 375808 1024).mp chunk_15
  by_cases e0 : i < 361472
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 362496
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 363520
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 364544
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 365568
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 366592
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 367616
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 368640
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 369664
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 370688
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 371712
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 372736
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 373760
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 374784
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 375808
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks22
