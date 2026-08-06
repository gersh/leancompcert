import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks57

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 933888 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 934912 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 935936 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 936960 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 937984 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 939008 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 940032 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 941056 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 942080 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 943104 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 944128 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 945152 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 946176 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 947200 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 948224 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 949248 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 933888 ≤ i) (hi : i < 950272) : leafOK i = true := by
  have h0 := (shardOK_iff 933888 1024).mp chunk_00
  have h1 := (shardOK_iff 934912 1024).mp chunk_01
  have h2 := (shardOK_iff 935936 1024).mp chunk_02
  have h3 := (shardOK_iff 936960 1024).mp chunk_03
  have h4 := (shardOK_iff 937984 1024).mp chunk_04
  have h5 := (shardOK_iff 939008 1024).mp chunk_05
  have h6 := (shardOK_iff 940032 1024).mp chunk_06
  have h7 := (shardOK_iff 941056 1024).mp chunk_07
  have h8 := (shardOK_iff 942080 1024).mp chunk_08
  have h9 := (shardOK_iff 943104 1024).mp chunk_09
  have h10 := (shardOK_iff 944128 1024).mp chunk_10
  have h11 := (shardOK_iff 945152 1024).mp chunk_11
  have h12 := (shardOK_iff 946176 1024).mp chunk_12
  have h13 := (shardOK_iff 947200 1024).mp chunk_13
  have h14 := (shardOK_iff 948224 1024).mp chunk_14
  have h15 := (shardOK_iff 949248 1024).mp chunk_15
  by_cases e0 : i < 934912
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 935936
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 936960
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 937984
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 939008
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 940032
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 941056
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 942080
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 943104
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 944128
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 945152
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 946176
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 947200
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 948224
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 949248
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks57
