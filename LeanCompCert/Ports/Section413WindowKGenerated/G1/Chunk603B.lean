import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk603A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk603B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk603A

def state06 : KState := ⟨⟨362500689538549267, 362500742982931863⟩, ⟨(-938427361536548151), (-936248335980367883)⟩, true⟩

def words05 : List Nat := [371285229145940962, 371285229355117166, 371285229838342147, 371285230224973792, 371285230693180580, 371285231162136212, 371285231571410469, 371285231649511233, 371285231907884432, 371285232167405607]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477842977671793, 362477896440274291⟩, ⟨440710054355298195, 442890179759431319⟩, true⟩

def words06 : List Nat := [371285232537846232, 371285232542940789, 371285232544486114, 371285232536009972, 371285232598597343, 371285232600849388, 371285232590901949, 371285232646708166, 371285232700867921, 371285232702983575]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498648672685111, 362498702153729376⟩, ⟨(-815407874257754419), (-813226635432515231)⟩, true⟩

def words07 : List Nat := [371285232705863572, 371285232831333260, 371285233230436306, 371285233264366061, 371285233265979494, 371285233218171263, 371285233364086795, 371285233450087385, 371285233674549122, 371285233899884086]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492473990040610, 362492527489580550⟩, ⟨(-442544882510503988), (-440362526826172750)⟩, true⟩

def words08 : List Nat := [371285234125291057, 371285234176845485, 371285234502305932, 371285234828852621, 371285235204266402, 371285235253476817, 371285235301315835, 371285235349826783, 371285235509617959, 371285235632733898]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491987954388276, 362492041472345064⟩, ⟨(-413151388772736511), (-410967920800739279)⟩, true⟩

def words09 : List Nat := [371285236004197937, 371285236376499479, 371285236726831057, 371285236728875820, 371285236760758572, 371285236810447795, 371285237133540419, 371285237251171894, 371285237365368909, 371285237480344920]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk603B
