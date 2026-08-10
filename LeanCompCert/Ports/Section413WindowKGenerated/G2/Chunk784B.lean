import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk784A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk784B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk784A

def state06 : KState := ⟨⟨360553420236760186, 360553460272455494⟩, ⟨2258028852823870786, 2260150403795031090⟩, true⟩

def words05 : List Nat := [360582267810900157, 360582267973202628, 360582268029852658, 360582268030973031, 360582267925434640, 360582267687577547, 360582267449376398, 360582267326684419, 360582267041759032, 360582266675766673]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570990266305466, 360571030312594165⟩, ⟨879325627509105246, 881448009689962016⟩, true⟩

def words06 : List Nat := [360582266309530406, 360582266041696413, 360582265856879558, 360582265587591911, 360582265318224262, 360582264910127252, 360582264339736366, 360582263931864481, 360582263523668360, 360582263242499734]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567822495165511, 360567862552133851⟩, ⟨1127930095494355287, 1130053315757660313⟩, true⟩

def words07 : List Nat := [360582263100360217, 360582262876439391, 360582262652306734, 360582262586347823, 360582262587287471, 360582262550548322, 360582262513704450, 360582262331256818, 360582261986561758, 360582261804373373]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360559973584575220, 360560013652097002⟩, ⟨1743893900579705978, 1746017949130292226⟩, true⟩

def words08 : List Nat := [360582261621809596, 360582261487636023, 360582261191314570, 360582260813962849, 360582260436424882, 360582259950905161, 360582259560571216, 360582259332542694, 360582259104413183, 360582258752735686]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582515552290712, 360582555630412510⟩, ⟨(-25605574951298759), (-23480694354439723)⟩, true⟩

def words09 : List Nat := [360582258470248304, 360582258184140892, 360582257897711037, 360582257723002348, 360582257500451536, 360582257139331845, 360582256777999089, 360582256579076838, 360582256512124910, 360582256517097337]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk784B
