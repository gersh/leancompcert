import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934A

def state06 : KState := ⟨⟨360556176492378958, 360556234076537006⟩, ⟨2409696222236764539, 2413330361880435643⟩, true⟩

def words05 : List Nat := [360582056780589094, 360582056903943155, 360582056969611016, 360582056970963816, 360582056922343629, 360582056845267623, 360582056767796061, 360582056635789198, 360582056418216112, 360582056143323658]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578405438454250, 360578463035381257⟩, ⟨332071048216615069, 335706381310218983⟩, true⟩

def words06 : List Nat := [360582055868132494, 360582055643310782, 360582055493348400, 360582055458095780, 360582055422727992, 360582055289199398, 360582055116534338, 360582054923809601, 360582054730691638, 360582054630345526]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593068293878695, 360593125903707130⟩, ⟨(-1038599184731714136), (-1034962645678096880)⟩, true⟩

def words07 : List Nat := [360582054593147205, 360582054468041105, 360582054342676349, 360582054342904784, 360582054344255494, 360582054345825653, 360582054347031053, 360582054295189783, 360582054414721755, 360582054534705108]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592180305618937, 360592237928179407⟩, ⟨(-955588717424150364), (-951950988114130216)⟩, true⟩

def words08 : List Nat := [360582054768613504, 360582054930381201, 360582055004913600, 360582055079571267, 360582055080723398, 360582055128192544, 360582055295201351, 360582055462466022, 360582055543763008, 360582055654076936]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603365551809306, 360603423187173001⟩, ⟨(-2001316338017031007), (-1997677411673735141)⟩, true⟩

def words09 : List Nat := [360582055878446817, 360582056103250479, 360582056441973747, 360582056666839119, 360582056784215106, 360582056901700766, 360582057133269949, 360582057422315228, 360582057651942162, 360582057881864248]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934B
