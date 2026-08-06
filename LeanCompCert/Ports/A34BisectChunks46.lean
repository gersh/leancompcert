import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks46

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 753664 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 754688 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 755712 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 756736 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 757760 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 758784 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 759808 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 760832 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 761856 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 762880 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 763904 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 764928 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 765952 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 766976 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 768000 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 769024 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 753664 ≤ i) (hi : i < 770048) : leafOK i = true := by
  have h0 := (shardOK_iff 753664 1024).mp chunk_00
  have h1 := (shardOK_iff 754688 1024).mp chunk_01
  have h2 := (shardOK_iff 755712 1024).mp chunk_02
  have h3 := (shardOK_iff 756736 1024).mp chunk_03
  have h4 := (shardOK_iff 757760 1024).mp chunk_04
  have h5 := (shardOK_iff 758784 1024).mp chunk_05
  have h6 := (shardOK_iff 759808 1024).mp chunk_06
  have h7 := (shardOK_iff 760832 1024).mp chunk_07
  have h8 := (shardOK_iff 761856 1024).mp chunk_08
  have h9 := (shardOK_iff 762880 1024).mp chunk_09
  have h10 := (shardOK_iff 763904 1024).mp chunk_10
  have h11 := (shardOK_iff 764928 1024).mp chunk_11
  have h12 := (shardOK_iff 765952 1024).mp chunk_12
  have h13 := (shardOK_iff 766976 1024).mp chunk_13
  have h14 := (shardOK_iff 768000 1024).mp chunk_14
  have h15 := (shardOK_iff 769024 1024).mp chunk_15
  by_cases e0 : i < 754688
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 755712
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 756736
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 757760
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 758784
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 759808
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 760832
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 761856
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 762880
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 763904
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 764928
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 765952
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 766976
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 768000
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 769024
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks46
