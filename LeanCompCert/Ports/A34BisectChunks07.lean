import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks07

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 114688 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 115712 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 116736 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 117760 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 118784 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 119808 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 120832 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 121856 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 122880 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 123904 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 124928 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 125952 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 126976 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 128000 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 129024 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 130048 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 114688 ≤ i) (hi : i < 131072) : leafOK i = true := by
  have h0 := (shardOK_iff 114688 1024).mp chunk_00
  have h1 := (shardOK_iff 115712 1024).mp chunk_01
  have h2 := (shardOK_iff 116736 1024).mp chunk_02
  have h3 := (shardOK_iff 117760 1024).mp chunk_03
  have h4 := (shardOK_iff 118784 1024).mp chunk_04
  have h5 := (shardOK_iff 119808 1024).mp chunk_05
  have h6 := (shardOK_iff 120832 1024).mp chunk_06
  have h7 := (shardOK_iff 121856 1024).mp chunk_07
  have h8 := (shardOK_iff 122880 1024).mp chunk_08
  have h9 := (shardOK_iff 123904 1024).mp chunk_09
  have h10 := (shardOK_iff 124928 1024).mp chunk_10
  have h11 := (shardOK_iff 125952 1024).mp chunk_11
  have h12 := (shardOK_iff 126976 1024).mp chunk_12
  have h13 := (shardOK_iff 128000 1024).mp chunk_13
  have h14 := (shardOK_iff 129024 1024).mp chunk_14
  have h15 := (shardOK_iff 130048 1024).mp chunk_15
  by_cases e0 : i < 115712
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 116736
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 117760
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 118784
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 119808
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 120832
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 121856
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 122880
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 123904
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 124928
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 125952
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 126976
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 128000
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 129024
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 130048
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks07
