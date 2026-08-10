import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk968A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk968B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk968A

def state06 : KState := ⟨⟨360614762499177515, 360614824520690945⟩, ⟨(-3149106791755407777), (-3145050345638792109)⟩, true⟩

def words05 : List Nat := [360582352016581521, 360582352353135895, 360582352739566315, 360582353048214235, 360582353249104243, 360582353450090641, 360582353757432340, 360582354119399671, 360582354455785937, 360582354792465563]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625297105162555, 360625359140058089⟩, ⟨(-4169646587780270615), (-4165588845406897261)⟩, true⟩

def words06 : List Nat := [360582355071807244, 360582355304892648, 360582355568951023, 360582355833411355, 360582356070267058, 360582356403082894, 360582356670814255, 360582356938681630, 360582357292213078, 360582357737725019]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599583707460206, 360599645755614949⟩, ⟨(-1678615783108887974), (-1674556756251769950)⟩, true⟩

def words07 : List Nat := [360582358263343433, 360582358789220362, 360582359233814654, 360582359572335708, 360582359868356486, 360582360164767505, 360582360476954470, 360582360719424756, 360582360899094460, 360582361078988451]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594534314786158, 360594596376204305⟩, ⟨(-1189371909019490268), (-1185311597137883392)⟩, true⟩

def words08 : List Nat := [360582361305345561, 360582361597882990, 360582361883746092, 360582362169869574, 360582362365117134, 360582362476344084, 360582362584775392, 360582362693608104, 360582362794429511, 360582362922146262]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587084789505972, 360587146864310976⟩, ⟨(-467492824430730098), (-463431215431027122)⟩, true⟩

def words09 : List Nat := [360582362996087606, 360582363070180944, 360582363250548247, 360582363513142134, 360582363748120839, 360582363983324173, 360582364164812375, 360582364240312382, 360582364290814558, 360582364341783541]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk968B
