import LeanCompCert.Ports.A34Bisect

namespace LeanCompCert.Ports.A34BisectChunks51

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem chunk_00 : shardOK 835584 1024 = true := by decide +kernel
theorem chunk_01 : shardOK 836608 1024 = true := by decide +kernel
theorem chunk_02 : shardOK 837632 1024 = true := by decide +kernel
theorem chunk_03 : shardOK 838656 1024 = true := by decide +kernel
theorem chunk_04 : shardOK 839680 1024 = true := by decide +kernel
theorem chunk_05 : shardOK 840704 1024 = true := by decide +kernel
theorem chunk_06 : shardOK 841728 1024 = true := by decide +kernel
theorem chunk_07 : shardOK 842752 1024 = true := by decide +kernel
theorem chunk_08 : shardOK 843776 1024 = true := by decide +kernel
theorem chunk_09 : shardOK 844800 1024 = true := by decide +kernel
theorem chunk_10 : shardOK 845824 1024 = true := by decide +kernel
theorem chunk_11 : shardOK 846848 1024 = true := by decide +kernel
theorem chunk_12 : shardOK 847872 1024 = true := by decide +kernel
theorem chunk_13 : shardOK 848896 1024 = true := by decide +kernel
theorem chunk_14 : shardOK 849920 1024 = true := by decide +kernel
theorem chunk_15 : shardOK 850944 1024 = true := by decide +kernel

theorem group_sound (i : Nat) (hlo : 835584 ≤ i) (hi : i < 851968) : leafOK i = true := by
  have h0 := (shardOK_iff 835584 1024).mp chunk_00
  have h1 := (shardOK_iff 836608 1024).mp chunk_01
  have h2 := (shardOK_iff 837632 1024).mp chunk_02
  have h3 := (shardOK_iff 838656 1024).mp chunk_03
  have h4 := (shardOK_iff 839680 1024).mp chunk_04
  have h5 := (shardOK_iff 840704 1024).mp chunk_05
  have h6 := (shardOK_iff 841728 1024).mp chunk_06
  have h7 := (shardOK_iff 842752 1024).mp chunk_07
  have h8 := (shardOK_iff 843776 1024).mp chunk_08
  have h9 := (shardOK_iff 844800 1024).mp chunk_09
  have h10 := (shardOK_iff 845824 1024).mp chunk_10
  have h11 := (shardOK_iff 846848 1024).mp chunk_11
  have h12 := (shardOK_iff 847872 1024).mp chunk_12
  have h13 := (shardOK_iff 848896 1024).mp chunk_13
  have h14 := (shardOK_iff 849920 1024).mp chunk_14
  have h15 := (shardOK_iff 850944 1024).mp chunk_15
  by_cases e0 : i < 836608
  · exact h0 i (by omega) e0
  ·
    by_cases e1 : i < 837632
    · exact h1 i (by omega) e1
    ·
      by_cases e2 : i < 838656
      · exact h2 i (by omega) e2
      ·
        by_cases e3 : i < 839680
        · exact h3 i (by omega) e3
        ·
          by_cases e4 : i < 840704
          · exact h4 i (by omega) e4
          ·
            by_cases e5 : i < 841728
            · exact h5 i (by omega) e5
            ·
              by_cases e6 : i < 842752
              · exact h6 i (by omega) e6
              ·
                by_cases e7 : i < 843776
                · exact h7 i (by omega) e7
                ·
                  by_cases e8 : i < 844800
                  · exact h8 i (by omega) e8
                  ·
                    by_cases e9 : i < 845824
                    · exact h9 i (by omega) e9
                    ·
                      by_cases e10 : i < 846848
                      · exact h10 i (by omega) e10
                      ·
                        by_cases e11 : i < 847872
                        · exact h11 i (by omega) e11
                        ·
                          by_cases e12 : i < 848896
                          · exact h12 i (by omega) e12
                          ·
                            by_cases e13 : i < 849920
                            · exact h13 i (by omega) e13
                            ·
                              by_cases e14 : i < 850944
                              · exact h14 i (by omega) e14
                              ·
                                exact h15 i (by omega) (by omega)

end LeanCompCert.Ports.A34BisectChunks51
