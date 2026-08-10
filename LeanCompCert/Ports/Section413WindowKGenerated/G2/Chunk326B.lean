import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk326A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk326B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk326A

def state06 : KState := ⟨⟨360625985695178136, 360625992157034953⟩, ⟨(-1458422383830050034), (-1458279680981624198)⟩, true⟩

def words05 : List Nat := [360581333213056807, 360581334156557348, 360581336035202665, 360581337447160342, 360581337968425392, 360581338489687778, 360581339239155342, 360581340462025460, 360581341829547856, 360581343197083280]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587928133875294, 360587934599890426⟩, ⟨(-215337783025978601), (-215194944346983321)⟩, true⟩

def words06 : List Nat := [360581343979023000, 360581344795059554, 360581346290236347, 360581347785449003, 360581348872404773, 360581349024611604, 360581349024999906, 360581348708397515, 360581348391739022, 360581347873302719]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360551749285368674, 360551755755484715⟩, ⟨966960531160062442, 967103503836565702⟩, true⟩

def words07 : List Nat := [360581348603859060, 360581349334453805, 360581349596507543, 360581349801329331, 360581349801694641, 360581349764272188, 360581350225587960, 360581350226023885, 360581349791075158, 360581348885957071]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586355565628845, 360586362039865039⟩, ⟨(-164329192584712817), (-164186085240947165)⟩, true⟩

def words08 : List Nat := [360581347980797226, 360581347221255209, 360581347066657156, 360581346402029497, 360581345737408523, 360581344273826038, 360581342226754554, 360581341113125428, 360581339999432606, 360581339676363129]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553165428873917, 360553171907261784⟩, ⟨920898253368492709, 921041496451085255⟩, true⟩

def words09 : List Nat := [360581339676752719, 360581339174231190, 360581339101639136, 360581340004408054, 360581340391436791, 360581340778511391, 360581340778910722, 360581340443429523, 360581339174767793, 360581338313881084]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk326B
