import LeanCompCert.Ports.A34BisectChunks00
import LeanCompCert.Ports.A34BisectChunks01
import LeanCompCert.Ports.A34BisectChunks02
import LeanCompCert.Ports.A34BisectChunks03
import LeanCompCert.Ports.A34BisectChunks04
import LeanCompCert.Ports.A34BisectChunks05
import LeanCompCert.Ports.A34BisectChunks06
import LeanCompCert.Ports.A34BisectChunks07
import LeanCompCert.Ports.A34BisectChunks08
import LeanCompCert.Ports.A34BisectChunks09
import LeanCompCert.Ports.A34BisectChunks10
import LeanCompCert.Ports.A34BisectChunks11
import LeanCompCert.Ports.A34BisectChunks12
import LeanCompCert.Ports.A34BisectChunks13
import LeanCompCert.Ports.A34BisectChunks14
import LeanCompCert.Ports.A34BisectChunks15
import LeanCompCert.Ports.A34BisectChunks16
import LeanCompCert.Ports.A34BisectChunks17
import LeanCompCert.Ports.A34BisectChunks18
import LeanCompCert.Ports.A34BisectChunks19
import LeanCompCert.Ports.A34BisectChunks20
import LeanCompCert.Ports.A34BisectChunks21
import LeanCompCert.Ports.A34BisectChunks22
import LeanCompCert.Ports.A34BisectChunks23
import LeanCompCert.Ports.A34BisectChunks24
import LeanCompCert.Ports.A34BisectChunks25
import LeanCompCert.Ports.A34BisectChunks26
import LeanCompCert.Ports.A34BisectChunks27
import LeanCompCert.Ports.A34BisectChunks28
import LeanCompCert.Ports.A34BisectChunks29
import LeanCompCert.Ports.A34BisectChunks30
import LeanCompCert.Ports.A34BisectChunks31
import LeanCompCert.Ports.A34BisectChunks32
import LeanCompCert.Ports.A34BisectChunks33
import LeanCompCert.Ports.A34BisectChunks34
import LeanCompCert.Ports.A34BisectChunks35
import LeanCompCert.Ports.A34BisectChunks36
import LeanCompCert.Ports.A34BisectChunks37
import LeanCompCert.Ports.A34BisectChunks38
import LeanCompCert.Ports.A34BisectChunks39
import LeanCompCert.Ports.A34BisectChunks40
import LeanCompCert.Ports.A34BisectChunks41
import LeanCompCert.Ports.A34BisectChunks42
import LeanCompCert.Ports.A34BisectChunks43
import LeanCompCert.Ports.A34BisectChunks44
import LeanCompCert.Ports.A34BisectChunks45
import LeanCompCert.Ports.A34BisectChunks46
import LeanCompCert.Ports.A34BisectChunks47
import LeanCompCert.Ports.A34BisectChunks48
import LeanCompCert.Ports.A34BisectChunks49
import LeanCompCert.Ports.A34BisectChunks50
import LeanCompCert.Ports.A34BisectChunks51
import LeanCompCert.Ports.A34BisectChunks52
import LeanCompCert.Ports.A34BisectChunks53
import LeanCompCert.Ports.A34BisectChunks54
import LeanCompCert.Ports.A34BisectChunks55
import LeanCompCert.Ports.A34BisectChunks56
import LeanCompCert.Ports.A34BisectChunks57
import LeanCompCert.Ports.A34BisectChunks58
import LeanCompCert.Ports.A34BisectChunks59
import LeanCompCert.Ports.A34BisectChunks60
import LeanCompCert.Ports.A34BisectChunks61
import LeanCompCert.Ports.A34BisectChunks62
import LeanCompCert.Ports.A34BisectChunks63

/-!
# Kernel-sharded certificate for the A.34 fixed-width sweep

Each imported block checked 16 independent 1,024-row shards.  The proof below
only dispatches an arbitrary index to its block; it performs no finite sweep.
-/

namespace LeanCompCert.Ports.A34BisectCertificate

open LeanCompCert.Ports.A34Bisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

theorem leaf_passes (i : Nat) (hi : i < leaves) : leafOK i = true := by
  have hi' : i < 1048576 := by simpa [leaves, depth] using hi
  by_cases e0 : i < 16384
  · exact A34BisectChunks00.group_sound i e0
  ·
    by_cases e1 : i < 32768
    · exact A34BisectChunks01.group_sound i (by omega) e1
    ·
      by_cases e2 : i < 49152
      · exact A34BisectChunks02.group_sound i (by omega) e2
      ·
        by_cases e3 : i < 65536
        · exact A34BisectChunks03.group_sound i (by omega) e3
        ·
          by_cases e4 : i < 81920
          · exact A34BisectChunks04.group_sound i (by omega) e4
          ·
            by_cases e5 : i < 98304
            · exact A34BisectChunks05.group_sound i (by omega) e5
            ·
              by_cases e6 : i < 114688
              · exact A34BisectChunks06.group_sound i (by omega) e6
              ·
                by_cases e7 : i < 131072
                · exact A34BisectChunks07.group_sound i (by omega) e7
                ·
                  by_cases e8 : i < 147456
                  · exact A34BisectChunks08.group_sound i (by omega) e8
                  ·
                    by_cases e9 : i < 163840
                    · exact A34BisectChunks09.group_sound i (by omega) e9
                    ·
                      by_cases e10 : i < 180224
                      · exact A34BisectChunks10.group_sound i (by omega) e10
                      ·
                        by_cases e11 : i < 196608
                        · exact A34BisectChunks11.group_sound i (by omega) e11
                        ·
                          by_cases e12 : i < 212992
                          · exact A34BisectChunks12.group_sound i (by omega) e12
                          ·
                            by_cases e13 : i < 229376
                            · exact A34BisectChunks13.group_sound i (by omega) e13
                            ·
                              by_cases e14 : i < 245760
                              · exact A34BisectChunks14.group_sound i (by omega) e14
                              ·
                                by_cases e15 : i < 262144
                                · exact A34BisectChunks15.group_sound i (by omega) e15
                                ·
                                  by_cases e16 : i < 278528
                                  · exact A34BisectChunks16.group_sound i (by omega) e16
                                  ·
                                    by_cases e17 : i < 294912
                                    · exact A34BisectChunks17.group_sound i (by omega) e17
                                    ·
                                      by_cases e18 : i < 311296
                                      · exact A34BisectChunks18.group_sound i (by omega) e18
                                      ·
                                        by_cases e19 : i < 327680
                                        · exact A34BisectChunks19.group_sound i (by omega) e19
                                        ·
                                          by_cases e20 : i < 344064
                                          · exact A34BisectChunks20.group_sound i (by omega) e20
                                          ·
                                            by_cases e21 : i < 360448
                                            · exact A34BisectChunks21.group_sound i (by omega) e21
                                            ·
                                              by_cases e22 : i < 376832
                                              · exact A34BisectChunks22.group_sound i (by omega) e22
                                              ·
                                                by_cases e23 : i < 393216
                                                · exact A34BisectChunks23.group_sound i (by omega) e23
                                                ·
                                                  by_cases e24 : i < 409600
                                                  · exact A34BisectChunks24.group_sound i (by omega) e24
                                                  ·
                                                    by_cases e25 : i < 425984
                                                    · exact A34BisectChunks25.group_sound i (by omega) e25
                                                    ·
                                                      by_cases e26 : i < 442368
                                                      · exact A34BisectChunks26.group_sound i (by omega) e26
                                                      ·
                                                        by_cases e27 : i < 458752
                                                        · exact A34BisectChunks27.group_sound i (by omega) e27
                                                        ·
                                                          by_cases e28 : i < 475136
                                                          · exact A34BisectChunks28.group_sound i (by omega) e28
                                                          ·
                                                            by_cases e29 : i < 491520
                                                            · exact A34BisectChunks29.group_sound i (by omega) e29
                                                            ·
                                                              by_cases e30 : i < 507904
                                                              · exact A34BisectChunks30.group_sound i (by omega) e30
                                                              ·
                                                                by_cases e31 : i < 524288
                                                                · exact A34BisectChunks31.group_sound i (by omega) e31
                                                                ·
                                                                  by_cases e32 : i < 540672
                                                                  · exact A34BisectChunks32.group_sound i (by omega) e32
                                                                  ·
                                                                    by_cases e33 : i < 557056
                                                                    · exact A34BisectChunks33.group_sound i (by omega) e33
                                                                    ·
                                                                      by_cases e34 : i < 573440
                                                                      · exact A34BisectChunks34.group_sound i (by omega) e34
                                                                      ·
                                                                        by_cases e35 : i < 589824
                                                                        · exact A34BisectChunks35.group_sound i (by omega) e35
                                                                        ·
                                                                          by_cases e36 : i < 606208
                                                                          · exact A34BisectChunks36.group_sound i (by omega) e36
                                                                          ·
                                                                            by_cases e37 : i < 622592
                                                                            · exact A34BisectChunks37.group_sound i (by omega) e37
                                                                            ·
                                                                              by_cases e38 : i < 638976
                                                                              · exact A34BisectChunks38.group_sound i (by omega) e38
                                                                              ·
                                                                                by_cases e39 : i < 655360
                                                                                · exact A34BisectChunks39.group_sound i (by omega) e39
                                                                                ·
                                                                                  by_cases e40 : i < 671744
                                                                                  · exact A34BisectChunks40.group_sound i (by omega) e40
                                                                                  ·
                                                                                    by_cases e41 : i < 688128
                                                                                    · exact A34BisectChunks41.group_sound i (by omega) e41
                                                                                    ·
                                                                                      by_cases e42 : i < 704512
                                                                                      · exact A34BisectChunks42.group_sound i (by omega) e42
                                                                                      ·
                                                                                        by_cases e43 : i < 720896
                                                                                        · exact A34BisectChunks43.group_sound i (by omega) e43
                                                                                        ·
                                                                                          by_cases e44 : i < 737280
                                                                                          · exact A34BisectChunks44.group_sound i (by omega) e44
                                                                                          ·
                                                                                            by_cases e45 : i < 753664
                                                                                            · exact A34BisectChunks45.group_sound i (by omega) e45
                                                                                            ·
                                                                                              by_cases e46 : i < 770048
                                                                                              · exact A34BisectChunks46.group_sound i (by omega) e46
                                                                                              ·
                                                                                                by_cases e47 : i < 786432
                                                                                                · exact A34BisectChunks47.group_sound i (by omega) e47
                                                                                                ·
                                                                                                  by_cases e48 : i < 802816
                                                                                                  · exact A34BisectChunks48.group_sound i (by omega) e48
                                                                                                  ·
                                                                                                    by_cases e49 : i < 819200
                                                                                                    · exact A34BisectChunks49.group_sound i (by omega) e49
                                                                                                    ·
                                                                                                      by_cases e50 : i < 835584
                                                                                                      · exact A34BisectChunks50.group_sound i (by omega) e50
                                                                                                      ·
                                                                                                        by_cases e51 : i < 851968
                                                                                                        · exact A34BisectChunks51.group_sound i (by omega) e51
                                                                                                        ·
                                                                                                          by_cases e52 : i < 868352
                                                                                                          · exact A34BisectChunks52.group_sound i (by omega) e52
                                                                                                          ·
                                                                                                            by_cases e53 : i < 884736
                                                                                                            · exact A34BisectChunks53.group_sound i (by omega) e53
                                                                                                            ·
                                                                                                              by_cases e54 : i < 901120
                                                                                                              · exact A34BisectChunks54.group_sound i (by omega) e54
                                                                                                              ·
                                                                                                                by_cases e55 : i < 917504
                                                                                                                · exact A34BisectChunks55.group_sound i (by omega) e55
                                                                                                                ·
                                                                                                                  by_cases e56 : i < 933888
                                                                                                                  · exact A34BisectChunks56.group_sound i (by omega) e56
                                                                                                                  ·
                                                                                                                    by_cases e57 : i < 950272
                                                                                                                    · exact A34BisectChunks57.group_sound i (by omega) e57
                                                                                                                    ·
                                                                                                                      by_cases e58 : i < 966656
                                                                                                                      · exact A34BisectChunks58.group_sound i (by omega) e58
                                                                                                                      ·
                                                                                                                        by_cases e59 : i < 983040
                                                                                                                        · exact A34BisectChunks59.group_sound i (by omega) e59
                                                                                                                        ·
                                                                                                                          by_cases e60 : i < 999424
                                                                                                                          · exact A34BisectChunks60.group_sound i (by omega) e60
                                                                                                                          ·
                                                                                                                            by_cases e61 : i < 1015808
                                                                                                                            · exact A34BisectChunks61.group_sound i (by omega) e61
                                                                                                                            ·
                                                                                                                              by_cases e62 : i < 1032192
                                                                                                                              · exact A34BisectChunks62.group_sound i (by omega) e62
                                                                                                                              ·
                                                                                                                                exact A34BisectChunks63.group_sound i (by omega) hi'

theorem sweep_ok : sweepOK = true := by
  unfold sweepOK sweepOKAt
  exact (LeanCompCert.Verified.DyadicBisect.allBelow_iff leaves leafOK).mpr leaf_passes

end LeanCompCert.Ports.A34BisectCertificate
