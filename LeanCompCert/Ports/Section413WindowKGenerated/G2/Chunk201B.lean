import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk201A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk201B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk201A

def state06 : KState := ⟨⟨360613785077751282, 360613787438499970⟩, ⟨(-638873723141743938), (-638841514983885232)⟩, true⟩

def words05 : List Nat := [360582071535690259, 360582075774035782, 360582079954174625, 360582085387457495, 360582089594162219, 360582093800491494, 360582096775350358, 360582097298845613, 360582098870986618, 360582100443064036]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575931248642876, 360575933611824084⟩, ⟨124571533432843895, 124603790642677435⟩, true⟩

def words06 : List Nat := [360582104463779990, 360582107769852379, 360582109003738971, 360582110237528899, 360582110268751781, 360582111550593719, 360582111897144644, 360582112243706952, 360582112243939659, 360582111291082522]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360732257258069749, 360732259623692746⟩, ⟨(-3029357019728521250), (-3029324713255765978)⟩, true⟩

def words07 : List Nat := [360582111776621126, 360582112568421872, 360582115806302767, 360582120415470170, 360582122910060314, 360582125404424489, 360582130343998671, 360582136985163004, 360582144424552169, 360582151863261858]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360642512051749854, 360642514419838111⟩, ⟨(-1218215371586917071), (-1218183015352748405)⟩, true⟩

def words08 : List Nat := [360582157433414440, 360582160558123781, 360582166126541926, 360582171694484017, 360582175609943698, 360582177080623249, 360582177305473270, 360582177530331701, 360582178460387788, 360582181448942527]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360535818489210025, 360535820859735206⟩, ⟨936713526922351901, 936745932370018021⟩, true⟩

def words09 : List Nat := [360582186023709487, 360582190598072757, 360582193705979971, 360582195765677907, 360582196089480114, 360582196413320315, 360582197785670087, 360582197785929066, 360582196716309866, 360582194420743623]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk201B
