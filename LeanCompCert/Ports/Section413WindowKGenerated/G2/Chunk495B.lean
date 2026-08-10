import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk495A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk495B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk495A

def state06 : KState := ⟨⟨360608992073813972, 360609007471352838⟩, ⟨(-1345263652507484583), (-1344748013688652713)⟩, true⟩

def words05 : List Nat := [360581868829903948, 360581869623213448, 360581870407844272, 360581871395266522, 360581872012282640, 360581872629383151, 360581873043140245, 360581873185343151, 360581873733399350, 360581874281673682]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578062606941295, 360578078010910750⟩, ⟨187748589189661788, 188264546741389462⟩, true⟩

def words06 : List Nat := [360581875051269831, 360581875414736914, 360581875573194493, 360581875731714771, 360581875732287495, 360581875908360184, 360581876026169778, 360581876144095944, 360581876144708376, 360581875964244246]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611461413439157, 360611476823858969⟩, ⟨(-1468020394385121663), (-1467504117057679843)⟩, true⟩

def words07 : List Nat := [360581875987704930, 360581876087987030, 360581876486086603, 360581876896494291, 360581876968447227, 360581877040449975, 360581877174584705, 360581877514078968, 360581878111632905, 360581878709317962]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591020466673211, 360591035883621604⟩, ⟨(-454574369454536668), (-454057768409186356)⟩, true⟩

def words08 : List Nat := [360581878992097148, 360581879157606160, 360581879650195679, 360581880142965805, 360581880462037256, 360581880462721073, 360581880376036748, 360581880086569940, 360581879796967683, 360581879831749104]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360546741042214861, 360546756465598077⟩, ⟨1741567278098383343, 1742084198279494015⟩, true⟩

def words09 : List Nat := [360581880318992681, 360581880806347598, 360581881048405458, 360581881049089435, 360581880989354434, 360581880600432362, 360581880226957620, 360581880227641680, 360581879838309121, 360581879130885971]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk495B
