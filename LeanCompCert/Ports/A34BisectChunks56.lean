import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks56

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 917504 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 918528 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 919552 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 920576 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 921600 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 922624 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 923648 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 924672 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 925696 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 926720 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 927744 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 928768 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 929792 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 930816 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 931840 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 932864 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 917504 ≤ i) (hi : i < 933888) : leafOK i = true := by
  have h0 := (shardOK_iff 917504 1024).mp chunk_00
  have h1 := (shardOK_iff 918528 1024).mp chunk_01
  have h2 := (shardOK_iff 919552 1024).mp chunk_02
  have h3 := (shardOK_iff 920576 1024).mp chunk_03
  have h4 := (shardOK_iff 921600 1024).mp chunk_04
  have h5 := (shardOK_iff 922624 1024).mp chunk_05
  have h6 := (shardOK_iff 923648 1024).mp chunk_06
  have h7 := (shardOK_iff 924672 1024).mp chunk_07
  have h8 := (shardOK_iff 925696 1024).mp chunk_08
  have h9 := (shardOK_iff 926720 1024).mp chunk_09
  have h10 := (shardOK_iff 927744 1024).mp chunk_10
  have h11 := (shardOK_iff 928768 1024).mp chunk_11
  have h12 := (shardOK_iff 929792 1024).mp chunk_12
  have h13 := (shardOK_iff 930816 1024).mp chunk_13
  have h14 := (shardOK_iff 931840 1024).mp chunk_14
  have h15 := (shardOK_iff 932864 1024).mp chunk_15
  by_cases e0 : i < 918528
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 919552
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 920576
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 921600
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 922624
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 923648
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 924672
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 925696
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 926720
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 927744
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 928768
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 929792
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 930816
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 931840
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 932864
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks56
