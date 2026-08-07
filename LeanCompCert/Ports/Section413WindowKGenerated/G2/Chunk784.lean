import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk784

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578145469338717, 360578185441449441⟩, ⟨318136875817676138, 320253439851759774⟩, true⟩

def state01 : KState := ⟨⟨360583946193473305, 360583986176150589⟩, ⟨(-136636478611897756), (-134519086107519984)⟩, true⟩

def words00 : List Nat := [360582270365896505, 360582270567330393, 360582270750996045, 360582270934869635, 360582270979541131, 360582270980660830, 360582270891262976, 360582270750029653, 360582270608450201, 360582270612184979]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571351258004881, 360571391251342639⟩, ⟨851027593902024210, 853145822348526902⟩, true⟩

def words01 : List Nat := [360582270613183010, 360582270536882555, 360582270460371649, 360582270576690025, 360582270657631697, 360582270738760185, 360582270739767449, 360582270738877040, 360582270575513680, 360582270438059657]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568549549990802, 360568589553892351⟩, ⟨1070632103216716218, 1072751160128333196⟩, true⟩

def words02 : List Nat := [360582270300255487, 360582270094196122, 360582269762630714, 360582269349893684, 360582268936985765, 360582268481867762, 360582268107990106, 360582267896690992, 360582267685260589, 360582267370545779]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596290099421082, 360596330113883683⟩, ⟨(-1105258865264427295), (-1103138979998036995)⟩, true⟩

def words03 : List Nat := [360582267197058451, 360582267153029405, 360582267160307608, 360582267161427723, 360582267051933327, 360582266794053406, 360582266535965610, 360582266457512962, 360582266637710497, 360582266818158259]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589228213363909, 360589268238507787⟩, ⟨(-551323985246667160), (-549203262088674266)⟩, true⟩

def words04 : List Nat := [360582266874851954, 360582267001669287, 360582267240572871, 360582267479810442, 360582267642303410, 360582267692674986, 360582267693673377, 360582267650684265, 360582267607497807, 360582267648813728]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk784
