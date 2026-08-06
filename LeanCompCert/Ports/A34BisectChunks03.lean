import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks03

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 49152 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 50176 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 51200 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 52224 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 53248 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 54272 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 55296 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 56320 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 57344 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 58368 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 59392 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 60416 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 61440 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 62464 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 63488 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 64512 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 49152 ≤ i) (hi : i < 65536) : leafOK i = true := by
  have h0 := (shardOK_iff 49152 1024).mp chunk_00
  have h1 := (shardOK_iff 50176 1024).mp chunk_01
  have h2 := (shardOK_iff 51200 1024).mp chunk_02
  have h3 := (shardOK_iff 52224 1024).mp chunk_03
  have h4 := (shardOK_iff 53248 1024).mp chunk_04
  have h5 := (shardOK_iff 54272 1024).mp chunk_05
  have h6 := (shardOK_iff 55296 1024).mp chunk_06
  have h7 := (shardOK_iff 56320 1024).mp chunk_07
  have h8 := (shardOK_iff 57344 1024).mp chunk_08
  have h9 := (shardOK_iff 58368 1024).mp chunk_09
  have h10 := (shardOK_iff 59392 1024).mp chunk_10
  have h11 := (shardOK_iff 60416 1024).mp chunk_11
  have h12 := (shardOK_iff 61440 1024).mp chunk_12
  have h13 := (shardOK_iff 62464 1024).mp chunk_13
  have h14 := (shardOK_iff 63488 1024).mp chunk_14
  have h15 := (shardOK_iff 64512 1024).mp chunk_15
  by_cases e0 : i < 50176
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 51200
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 52224
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 53248
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 54272
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 55296
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 56320
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 57344
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 58368
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 59392
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 60416
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 61440
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 62464
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 63488
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 64512
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks03
