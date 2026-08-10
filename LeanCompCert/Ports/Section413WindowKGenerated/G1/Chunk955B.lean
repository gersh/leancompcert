import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk955A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk955B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk955A

def state06 : KState := ⟨⟨362478899869949913, 362479038691607053⟩, ⟨582442877980722761, 591399435801177077⟩, true⟩

def words05 : List Nat := [371285226789169723, 371285227010015154, 371285227229111665, 371285227302972525, 371285227398924871, 371285227496494697, 371285227583802721, 371285227587152381, 371285227528589507, 371285227467620042]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490513276635691, 362490652128286743⟩, ⟨(-527377448661654660), (-518418024471360790)⟩, true⟩

def words06 : List Nat := [371285227450022408, 371285227453748705, 371285227508372659, 371285227574336302, 371285227613092551, 371285227616442951, 371285227523247126, 371285227527653872, 371285227639883950, 371285227700118456]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491264786997604, 362491403669198047⟩, ⟨(-599201991319577372), (-590239647372510284)⟩, true⟩

def words07 : List Nat := [371285227722592252, 371285227746097400, 371285227859992387, 371285227930207836, 371285228032802771, 371285228136724647, 371285228239027854, 371285228251341502, 371285228318238369, 371285228387004175]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488278276853474, 362488417188875855⟩, ⟨(-313734431455253504), (-304769236974120840)⟩, true⟩

def words08 : List Nat := [371285228563485445, 371285228595077915, 371285228621097019, 371285228648299013, 371285228680453669, 371285228684146709, 371285228738726228, 371285228814982983, 371285228889149072, 371285228925995730]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499658061476746, 362499797003837973⟩, ⟨(-1401582381023092936), (-1392614286298710236)⟩, true⟩

def words09 : List Nat := [371285229030320375, 371285229136475909, 371285229341074609, 371285229400822752, 371285229443458940, 371285229487108189, 371285229638984256, 371285229750288577, 371285229904977980, 371285230061166885]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk955B
