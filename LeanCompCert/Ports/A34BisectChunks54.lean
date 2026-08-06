import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks54

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 884736 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 885760 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 886784 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 887808 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 888832 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 889856 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 890880 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 891904 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 892928 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 893952 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 894976 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 896000 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 897024 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 898048 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 899072 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 900096 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 884736 ≤ i) (hi : i < 901120) : leafOK i = true := by
  have h0 := (shardOK_iff 884736 1024).mp chunk_00
  have h1 := (shardOK_iff 885760 1024).mp chunk_01
  have h2 := (shardOK_iff 886784 1024).mp chunk_02
  have h3 := (shardOK_iff 887808 1024).mp chunk_03
  have h4 := (shardOK_iff 888832 1024).mp chunk_04
  have h5 := (shardOK_iff 889856 1024).mp chunk_05
  have h6 := (shardOK_iff 890880 1024).mp chunk_06
  have h7 := (shardOK_iff 891904 1024).mp chunk_07
  have h8 := (shardOK_iff 892928 1024).mp chunk_08
  have h9 := (shardOK_iff 893952 1024).mp chunk_09
  have h10 := (shardOK_iff 894976 1024).mp chunk_10
  have h11 := (shardOK_iff 896000 1024).mp chunk_11
  have h12 := (shardOK_iff 897024 1024).mp chunk_12
  have h13 := (shardOK_iff 898048 1024).mp chunk_13
  have h14 := (shardOK_iff 899072 1024).mp chunk_14
  have h15 := (shardOK_iff 900096 1024).mp chunk_15
  by_cases e0 : i < 885760
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 886784
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 887808
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 888832
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 889856
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 890880
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 891904
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 892928
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 893952
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 894976
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 896000
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 897024
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 898048
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 899072
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 900096
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks54
