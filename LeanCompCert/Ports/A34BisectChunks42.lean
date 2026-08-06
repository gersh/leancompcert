import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks42

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 688128 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 689152 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 690176 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 691200 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 692224 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 693248 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 694272 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 695296 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 696320 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 697344 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 698368 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 699392 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 700416 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 701440 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 702464 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 703488 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 688128 ≤ i) (hi : i < 704512) : leafOK i = true := by
  have h0 := (shardOK_iff 688128 1024).mp chunk_00
  have h1 := (shardOK_iff 689152 1024).mp chunk_01
  have h2 := (shardOK_iff 690176 1024).mp chunk_02
  have h3 := (shardOK_iff 691200 1024).mp chunk_03
  have h4 := (shardOK_iff 692224 1024).mp chunk_04
  have h5 := (shardOK_iff 693248 1024).mp chunk_05
  have h6 := (shardOK_iff 694272 1024).mp chunk_06
  have h7 := (shardOK_iff 695296 1024).mp chunk_07
  have h8 := (shardOK_iff 696320 1024).mp chunk_08
  have h9 := (shardOK_iff 697344 1024).mp chunk_09
  have h10 := (shardOK_iff 698368 1024).mp chunk_10
  have h11 := (shardOK_iff 699392 1024).mp chunk_11
  have h12 := (shardOK_iff 700416 1024).mp chunk_12
  have h13 := (shardOK_iff 701440 1024).mp chunk_13
  have h14 := (shardOK_iff 702464 1024).mp chunk_14
  have h15 := (shardOK_iff 703488 1024).mp chunk_15
  by_cases e0 : i < 689152
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 690176
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 691200
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 692224
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 693248
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 694272
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 695296
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 696320
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 697344
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 698368
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 699392
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 700416
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 701440
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 702464
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 703488
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks42
