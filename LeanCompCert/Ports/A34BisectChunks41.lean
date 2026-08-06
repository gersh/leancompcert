import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks41

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 671744 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 672768 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 673792 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 674816 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 675840 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 676864 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 677888 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 678912 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 679936 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 680960 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 681984 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 683008 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 684032 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 685056 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 686080 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 687104 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 671744 ≤ i) (hi : i < 688128) : leafOK i = true := by
  have h0 := (shardOK_iff 671744 1024).mp chunk_00
  have h1 := (shardOK_iff 672768 1024).mp chunk_01
  have h2 := (shardOK_iff 673792 1024).mp chunk_02
  have h3 := (shardOK_iff 674816 1024).mp chunk_03
  have h4 := (shardOK_iff 675840 1024).mp chunk_04
  have h5 := (shardOK_iff 676864 1024).mp chunk_05
  have h6 := (shardOK_iff 677888 1024).mp chunk_06
  have h7 := (shardOK_iff 678912 1024).mp chunk_07
  have h8 := (shardOK_iff 679936 1024).mp chunk_08
  have h9 := (shardOK_iff 680960 1024).mp chunk_09
  have h10 := (shardOK_iff 681984 1024).mp chunk_10
  have h11 := (shardOK_iff 683008 1024).mp chunk_11
  have h12 := (shardOK_iff 684032 1024).mp chunk_12
  have h13 := (shardOK_iff 685056 1024).mp chunk_13
  have h14 := (shardOK_iff 686080 1024).mp chunk_14
  have h15 := (shardOK_iff 687104 1024).mp chunk_15
  by_cases e0 : i < 672768
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 673792
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 674816
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 675840
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 676864
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 677888
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 678912
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 679936
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 680960
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 681984
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 683008
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 684032
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 685056
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 686080
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 687104
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks41
