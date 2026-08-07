import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk114

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360620621415486911, 360620622131618953⟩, ⟨(-405402811424214049), (-405397279305543147)⟩, true⟩

def state01 : KState := ⟨⟨360493212482965581, 360493213200408665⟩, ⟨1047287103735928427, 1047292650807176879⟩, true⟩

def words00 : List Nat := [360585069310451361, 360585069310590384, 360585066911748557, 360585058643603790, 360585050376886398, 360585040127524683, 360585033760390157, 360585023938063478, 360585014117443264, 360585000461653817]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360635031894394222, 360635032613150340⟩, ⟨(-571467209500041510), (-571461647440418194)⟩, true⟩

def words01 : List Nat := [360584992418013888, 360584992000437833, 360584996217109192, 360584998867255045, 360584998867383320, 360584994970578309, 360584991074431410, 360584987806216683, 360584992188536935, 360584996570120797]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360552978728003175, 360552979448086699⟩, ⟨365429415048949102, 365434992274096004⟩, true⟩

def words02 : List Nat := [360584996615342687, 360584996615481969, 360584989119698018, 360584989176653055, 360584989176769841, 360584987135838444, 360584981445535225, 360584970936298164, 360584960428874400, 360584951013465011]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360416361222714019, 360416361944112587⟩, ⟨1927221339152002986, 1927226931414636488⟩, true⟩

def words03 : List Nat := [360584948216662347, 360584942052331092, 360584935889063098, 360584924500381329, 360584905531710613, 360584884587097442, 360584863646106465, 360584850300385462, 360584840563725005, 360584825836718762]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360640517893464368, 360640518616178861⟩, ⟨(-638392418551758202), (-638386811228288750)⟩, true⟩

def words04 : List Nat := [360584811112254431, 360584798859602383, 360584790462777843, 360584789651144132, 360584788839643523, 360584781061271074, 360584769591475632, 360584765702734935, 360584764309376780, 360584769178467894]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360522561175635848, 360522561899682791⟩, ⟨712829188168962308, 712834810755542756⟩, true⟩

def words05 : List Nat := [360584769178593196, 360584768042033829, 360584767858066290, 360584773774553844, 360584775748993184, 360584777723110488, 360584777723236485, 360584774557445512, 360584769318212573, 360584763890150116]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360666371656151484, 360666372381515839⟩, ⟨(-936172459270807396), (-936166821580155046)⟩, true⟩

def words06 : List Nat := [360584758462989131, 360584757929008883, 360584756506214724, 360584751281588693, 360584746057851376, 360584738871603881, 360584744385639119, 360584750916738721, 360584753652375294, 360584760767743705]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360637361101997846, 360637361828685618⟩, ⟨(-603424157987997512), (-603418505111239256)⟩, true⟩

def words07 : List Nat := [360584775427005332, 360584790083752151, 360584800249955030, 360584802885936339, 360584802886067128, 360584798206057591, 360584793526836884, 360584794661849618, 360584799240985047, 360584803819356184]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566231605578029, 360566232333598909⟩, ⟨212699029526833003, 212704697714335751⟩, true⟩

def words08 : List Nat := [360584803819481099, 360584803646239311, 360584795954351953, 360584795794095035, 360584795633826791, 360584793521499887, 360584783893474658, 360584768249038851, 360584752607299805, 360584744491798591]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360502286778907736, 360502287508249295⟩, ⟨948265935539274657, 948271618908064997⟩, true⟩

def words09 : List Nat := [360584748792333879, 360584754702881786, 360584756730430417, 360584759154482732, 360584759154601194, 360584755753346946, 360584756468054629, 360584756468194909, 360584753080667394, 360584745909893475]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk114
